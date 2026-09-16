#!/usr/bin/env python3
"""
streams.py — all-in-one terminal stream browser.

Combines four scripts into one app:

    dlhd      DaddyLive 24/7 TV channels          https://dlhd.st
    bintv     live event index                   https://bintv.cc
    ppv       event index + substreams           https://ppv.st
    streamed  sports streams (Streamed.pk/.st)   https://streamed.pk

Run without arguments for an interactive source picker, or jump straight
into a source with a subcommand:

    python streams.py                          # source picker
    python streams.py dlhd                     # DaddyLive 24/7 channels
    python streams.py dlhd --play --id 42
    python streams.py dlhd --play --channel espn
    python streams.py bintv --live-only        # only live events
    python streams.py bintv --json
    python streams.py ppv --show-default
    python streams.py streamed --base https://streamed.st
    python streams.py streamed --play

`--raw` (disable ANSI colours) is accepted anywhere on the command line.

Dependencies — only install what you use:
    pip install httpx                  # dlhd, ppv, streamed
    pip install playwright             # bintv only
    playwright install chromium        # bintv only

Python 3.10+.
"""

from __future__ import annotations

import argparse
import base64
import json
import os
import re
import shutil
import subprocess
import sys
import threading
import time
import urllib.parse
import webbrowser
from dataclasses import dataclass, field
from datetime import datetime
from html.parser import HTMLParser
from typing import Any
from urllib.parse import parse_qs, urlparse

try:
    import httpx
except ImportError:  # checked lazily — only dlhd / ppv / streamed need it
    httpx = None


# =========================================================================
# Shared config
# =========================================================================

USER_AGENT = (
    "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 "
    "(KHTML, like Gecko) Chrome/120.0.0.0 Safari/537.36"
)
TIMEOUT = 15.0
MAX_RETRIES = 3
RETRY_BACKOFF_BASE = 0.75  # seconds; doubles each attempt


def _require_httpx() -> None:
    if httpx is None:
        sys.stderr.write(
            "error: this source needs the httpx package.\n"
            "        install with: pip install httpx\n"
        )
        sys.exit(2)


# =========================================================================
# Shared terminal helpers
# =========================================================================

def enable_colors(disable: bool) -> bool:
    if disable:
        return False
    if not sys.stdout.isatty():
        return False
    if os.environ.get("NO_COLOR"):
        return False
    return os.environ.get("TERM", "") != "dumb"


class C:
    """ANSI palette — 256-color sky/amber/slate theme."""

    def __init__(self, on: bool):
        self.on = on
        if not on:
            return
        self.dim = "\033[2m"
        self.bold = "\033[1m"
        self.reset = "\033[0m"
        self.sky = "\033[38;5;110m"
        self.amber = "\033[38;5;179m"
        self.slate = "\033[38;5;246m"
        self.sage = "\033[38;5;108m"
        self.warn = "\033[38;5;173m"
        self.rose = "\033[38;5;204m"
        self.bg_sel = "\033[48;5;237m"

    def __getattr__(self, name: str) -> str:
        return ""


def _term_height(default: int = 24) -> int:
    try:
        return max(10, os.get_terminal_size().lines)
    except (OSError, ValueError):
        return default


def _term_width(default: int = 100) -> int:
    try:
        return max(40, os.get_terminal_size().columns)
    except (OSError, ValueError):
        return default


def truncate_str(s: str, width: int) -> str:
    if width <= 0:
        return ""
    if len(s) > width:
        return s[: width - 3] + "..." if width >= 3 else s[:width]
    return s.ljust(width)


def pause(c: C, message: str = "Press Enter to continue...") -> None:
    try:
        input(f"  {c.dim}{message}{c.reset}")
    except (EOFError, KeyboardInterrupt):
        pass


def print_banner(title: str, sub: str, c: C) -> None:
    need = max(len(title), len(sub)) + 6
    w = min(_term_width(), max(need, 24))
    inner = w - 2
    t_pad = max(0, inner - len(title) - 2)
    s_pad = max(0, inner - len(sub) - 2)

    print(f"{c.sky}╭{'─' * inner}╮{c.reset}")
    print(f"{c.sky}│{c.reset}  {c.bold}{c.sky}{title}{c.reset}{' ' * t_pad}{c.sky}│{c.reset}")
    print(f"{c.sky}│{c.reset}  {c.slate}{sub}{c.reset}{' ' * s_pad}{c.sky}│{c.reset}")
    print(f"{c.sky}╰{'─' * inner}╯{c.reset}")
    print()


def fetch_with_spinner(label: str, fn, c: C, quiet: bool = False):
    """Call fn() while animating a braille spinner. Returns fn()'s result."""
    if not sys.stdout.isatty() or quiet:
        if not quiet:
            sys.stderr.write(f"  {label}…\n")
            sys.stderr.flush()
        return fn()

    frames = "⠋⠙⠹⠸⠼⠴⠦⠧⠇⠏"
    result = [None]
    exc = [None]
    done = threading.Event()

    def worker() -> None:
        try:
            result[0] = fn()
        except Exception as e:
            exc[0] = e
        finally:
            done.set()

    threading.Thread(target=worker, daemon=True).start()

    i = 0
    while not done.wait(0.08):
        sys.stdout.write(
            f"\r  {c.sky}{frames[i % len(frames)]}{c.reset}"
            f"  {c.slate}{label}{c.reset}\033[K"
        )
        sys.stdout.flush()
        i += 1

    sys.stdout.write("\r\033[K")
    sys.stdout.flush()

    if exc[0]:
        raise exc[0]
    return result[0]


# =========================================================================
# Shared selection prompt — arrow keys + live filter, no third-party deps
# =========================================================================

ANSI_RE = re.compile(r"\x1b\[[0-9;?]*[ -/]*[@-~]")


def strip_ansi(s: str) -> str:
    return ANSI_RE.sub("", s)


def _read_key() -> str:
    ch = sys.stdin.read(1)
    if ch == "":
        return "CTRL_D"  # EOF
    if ch == "\x1b":
        nxt = sys.stdin.read(1)
        if nxt in ("[", "O"):
            code = sys.stdin.read(1)
            if code == "A":
                return "UP"
            if code == "B":
                return "DOWN"
            if code == "C":
                return "RIGHT"
            if code == "D":
                return "LEFT"
            if code == "H":
                return "UP"
            if code == "F":
                return "DOWN"
            while code not in ("~",):
                code = sys.stdin.read(1)
                if not code:
                    return "?"
            return "?"
        return "ESC"
    if ch in ("\r", "\n"):
        return "ENTER"
    if ch in ("\x7f", "\b"):
        return "BACK"
    if ch == "\x03":
        return "CTRL_C"
    if ch == "\x04":
        return "CTRL_D"
    if ch.isprintable():
        return "TEXT:" + ch
    return ""


def _pick_plain(title: str, rows: list[str], header_row: str | None = None) -> int | None:
    print(strip_ansi(title))
    if header_row:
        print(f"       {strip_ansi(header_row)}")
    for i, r in enumerate(rows, 1):
        print(f"  {i:>3}.  {strip_ansi(r)}")
    try:
        q = input(f"  Enter number (1–{len(rows)}): ").strip()
    except (EOFError, KeyboardInterrupt):
        return None
    if not q.isdigit():
        return None
    n = int(q)
    return n - 1 if 1 <= n <= len(rows) else None


def _clear_block(out, block_height: int) -> None:
    if block_height > 1:
        out.write(f"\033[{block_height - 1}A")
    out.write("\r")
    for i in range(block_height):
        out.write("\033[2K")
        if i < block_height - 1:
            out.write("\r\n")
    if block_height > 1:
        out.write(f"\033[{block_height - 1}A")
    out.write("\r")
    out.flush()


def pick_from_list(
    title: str,
    rows: list[str],
    *,
    c: C,
    header_row: str | None = None,
) -> int | None:
    """
    Filterable arrow-key picker on a TTY; numbered-list fallback otherwise.
    Returns the chosen row index, or None if cancelled.
    """
    if not sys.stdin.isatty() or not sys.stdout.isatty():
        return _pick_plain(title, rows, header_row)

    import termios  # type: ignore
    import tty  # type: ignore

    fd = sys.stdin.fileno()
    old = termios.tcgetattr(fd)

    try:
        tty.setraw(fd)

        out = sys.stdout
        out.write("\033[?25l")  # hide cursor
        out.flush()

        header_len = 1 if header_row is not None else 0
        block_height = max(8, _term_height() - 1)
        list_room = max(3, block_height - 3 - header_len)

        query = ""
        cursor = 0
        scroll = 0
        first_render = True

        def filtered() -> list[int]:
            if not query:
                return list(range(len(rows)))
            q = query.lower()
            return [i for i, r in enumerate(rows) if q in strip_ansi(r).lower()]

        def render() -> None:
            nonlocal cursor, scroll, first_render

            idxs = filtered()

            if not idxs:
                cursor, scroll = 0, 0
            else:
                cursor = max(0, min(cursor, len(idxs) - 1))
                if cursor < scroll:
                    scroll = cursor
                elif cursor >= scroll + list_room:
                    scroll = cursor - list_room + 1

            if not first_render:
                out.write(f"\033[{block_height - 1}A\r")
            else:
                first_render = False

            out.write(f"{c.bold}{title}{c.reset}\033[K\r\n")
            out.write(f"  {c.slate}filter ›{c.reset} {query}{c.dim}▌{c.reset}\033[K\r\n")

            if header_row is not None:
                out.write(f"  {header_row}\033[K\r\n")

            end = min(len(idxs), scroll + list_room)

            for k in range(list_room):
                screen_i = scroll + k
                if screen_i < end:
                    r = rows[idxs[screen_i]]
                    if screen_i == cursor:
                        out.write(f"{c.bg_sel}  {r}{c.reset}\033[K\r\n")
                    else:
                        out.write(f"  {r}\033[K\r\n")
                else:
                    out.write("\033[K\r\n")

            if idxs:
                pct = f"{len(idxs)}/{len(rows)}"
                legend = (
                    f"{c.dim}  ↑↓ navigate · type to filter · "
                    f"Enter select · Esc cancel  [{pct}]{c.reset}"
                )
            else:
                legend = f"{c.warn}  no matches — keep typing or press Esc{c.reset}"

            out.write(f"{legend}\033[K")
            out.flush()

        render()

        while True:
            key = _read_key()

            if key == "UP":
                if filtered():
                    cursor = max(0, cursor - 1)
                render()
            elif key == "DOWN":
                idxs = filtered()
                if idxs:
                    cursor = min(len(idxs) - 1, cursor + 1)
                render()
            elif key == "ENTER":
                idxs = filtered()
                if not idxs:
                    continue
                _clear_block(out, block_height)
                out.write("\033[?25h")
                out.flush()
                return idxs[cursor]
            elif key in ("ESC", "CTRL_C", "CTRL_D"):
                _clear_block(out, block_height)
                out.write("\033[?25h")
                out.flush()
                return None
            elif key == "BACK":
                query = query[:-1]
                cursor = 0
                scroll = 0
                render()
            elif key.startswith("TEXT:"):
                query += key.split(":", 1)[1]
                cursor = 0
                scroll = 0
                render()
    finally:
        try:
            termios.tcsetattr(fd, termios.TCSAFLUSH, old)
        except Exception:
            pass
        sys.stdout.write("\033[?25h")
        sys.stdout.flush()


# =========================================================================
# Shared playback actions
# =========================================================================

def is_valid_url(url: str | None) -> bool:
    if not url:
        return False
    try:
        parsed = urllib.parse.urlparse(url)
    except ValueError:
        return False
    return parsed.scheme in ("http", "https") and bool(parsed.netloc)


def _require_binary(cmd: str, c: C) -> bool:
    if shutil.which(cmd) is None:
        sys.stderr.write(f"\n  {c.rose}✗ '{cmd}' was not found in your PATH.{c.reset}\n")
        pause(c)
        return False
    return True


def play_with_mpv(stream_url: str, c: C, referer: str | None = None) -> None:
    """Play a stream in mpv, deriving Origin from the actual referer."""
    if not _require_binary("mpv", c):
        return
    if not is_valid_url(stream_url):
        sys.stderr.write(
            f"\n  {c.rose}✗ Resolved value doesn't look like a playable URL: "
            f"{stream_url!r}{c.reset}\n"
        )
        pause(c)
        return

    effective_referer = referer or stream_url
    parsed = urllib.parse.urlparse(effective_referer)
    origin = f"{parsed.scheme}://{parsed.netloc}"

    cmd = [
        "mpv",
        stream_url,
        f"--http-header-fields=Referer: {effective_referer},Origin: {origin}",
        f"--user-agent={USER_AGENT}",
        "--demuxer-readahead-secs=10",
    ]
    print(f"\n  {c.sky}▶ Launching mpv…{c.reset}  {c.dim}(close the player to return){c.reset}\n")
    try:
        subprocess.run(cmd)
    except KeyboardInterrupt:
        pass
    except Exception as e:
        sys.stderr.write(f"  {c.rose}✗ mpv exited with an error: {e}{c.reset}\n")


def open_in_browser(url: str, c: C) -> None:
    if not is_valid_url(url):
        sys.stderr.write(f"\n  {c.rose}✗ Invalid URL: {url!r}{c.reset}\n")
        pause(c)
        return
    print(f"\n  {c.sky}▶ Opening URL in your browser…{c.reset}\n")
    try:
        opened = webbrowser.open(url, new=2)
        if not opened:
            sys.stderr.write(
                f"  {c.rose}✗ Could not find a browser to open the URL.{c.reset}\n"
                f"  {c.dim}URL: {url}{c.reset}\n"
            )
    except Exception as e:
        sys.stderr.write(f"  {c.rose}✗ Failed to open browser: {e}{c.reset}\n")


def choose_playback_action(
    c: C,
    allow_mpv: bool = True,
    back_label: str = "Back to list",
) -> str | None:
    rows: list[str] = []
    actions: list[str] = []

    if allow_mpv:
        rows.append(f"{c.sage}▶{c.reset}  Play in {c.bold}mpv{c.reset}")
        actions.append("mpv")
    rows.append(f"{c.amber}⊞{c.reset}  Open embed URL in browser")
    actions.append("browser")
    rows.append(f"{c.slate}i{c.reset}  Show stream details")
    actions.append("details")
    rows.append(f"{c.dim}←{c.reset}  {back_label}")
    actions.append("back")

    idx = pick_from_list("What would you like to do?", rows, c=c)
    if idx is None:
        return None
    return actions[idx]


# =========================================================================
# Shared HTTP plumbing (retry + m3u8 extraction) — used by dlhd & streamed
# =========================================================================

class _HttpRetryClient:
    """Owns an httpx.Client and retries transport errors / 5xx responses."""

    def __init__(self, client: httpx.Client):
        self.client = client
        self._owns_client = True

    def close(self) -> None:
        if self._owns_client and self.client is not None:
            self.client.close()

    def __enter__(self):
        return self

    def __exit__(self, *exc) -> None:
        self.close()

    def _get_with_retry(self, url: str) -> httpx.Response:
        last_exc: Exception | None = None
        for attempt in range(MAX_RETRIES):
            try:
                r = self.client.get(url)
                if r.status_code >= 500:
                    r.raise_for_status()
                return r
            except (httpx.TransportError, httpx.HTTPStatusError) as e:
                last_exc = e
                if isinstance(e, httpx.HTTPStatusError) and e.response.status_code < 500:
                    raise
                if attempt < MAX_RETRIES - 1:
                    time.sleep(RETRY_BACKOFF_BASE * (2 ** attempt))
        assert last_exc is not None
        raise last_exc


def _follow_nested_iframe(get, html: str, current_url: str) -> tuple[str, str]:
    """If html wraps a player in a nested iframe, fetch it.

    Returns (html, referer) — either the nested page + its URL, or the
    original pair when there is no usable nested iframe.
    """
    nested = re.search(r'<iframe[^>]+src=["\'](https?://[^"\']+)["\']', html, re.IGNORECASE)
    if nested:
        nested_url = nested.group(1)
        if nested_url != current_url and "histats" not in nested_url:
            try:
                r2 = get(nested_url)
                r2.raise_for_status()
                return r2.text, nested_url
            except Exception:
                pass
    return html, current_url


def _extract_stream_from_html(html: str) -> str | None:
    """The base64 / m3u8 / file: scraping cascade shared by dlhd + streamed."""
    match = re.search(r'window\.atob\([\'"]([A-Za-z0-9+/=]+)[\'"]\)', html)
    if match:
        try:
            return base64.b64decode(match.group(1)).decode("utf-8")
        except Exception:
            pass

    m3u8_match = re.search(r'(https?://[^\s\'"<>]+\.m3u8(?:[^\s\'"<>]*))', html)
    if m3u8_match:
        return m3u8_match.group(1)

    for b64_str in re.findall(r'atob\(["\']([A-Za-z0-9+/=]{20,})["\']\)', html):
        try:
            decoded = base64.b64decode(b64_str).decode("utf-8")
            if ".m3u8" in decoded or "http" in decoded:
                clean_url = re.search(r'(https?://[^\s\'"<>]+)', decoded)
                if clean_url:
                    return clean_url.group(1)
        except Exception:
            continue

    file_match = re.search(r'file\s*:\s*["\'](https?://[^"\']+)["\']', html)
    if file_match:
        return file_match.group(1)

    iframe_match = re.search(r'<iframe[^>]*id=["\']playerFrame["\'][^>]*src=["\']([^"\']+)["\']', html)
    if iframe_match:
        return iframe_match.group(1)

    player_match = re.search(r'data-url=["\']([^"\']*stream[^"\']*)["\']', html)
    if player_match:
        return player_match.group(1)

    return None


# =========================================================================
# Source 1 — DaddyLive (dlhd.st)
# =========================================================================

DLHD_API_BASE = "https://dlhd.st"
DLHD_CHANNELS_ENDPOINT = f"{DLHD_API_BASE}/24-7-channels.php"
DLHD_REFERER = "https://dlhd.st/24-7-channels.php"
DLHD_ORIGIN = "https://dlhd.st"


class DaddyLiveClient(_HttpRetryClient):
    def __init__(self, client: httpx.Client | None = None):
        _require_httpx()
        client = client or httpx.Client(
            headers={
                "User-Agent": USER_AGENT,
                "Referer": DLHD_REFERER,
                "Origin": DLHD_ORIGIN,
                "Accept": "application/json, text/plain, */*",
                "X-Requested-With": "XMLHttpRequest",
                "Accept-Language": "en-US,en;q=0.9",
                "Accept-Encoding": "gzip, deflate, br",
                "Connection": "keep-alive",
            },
            timeout=TIMEOUT,
            follow_redirects=True,
        )
        super().__init__(client)

    def fetch_channels(self) -> list[dict[str, Any]]:
        r = self._get_with_retry(DLHD_CHANNELS_ENDPOINT)
        r.raise_for_status()

        class ChannelParser(HTMLParser):
            def __init__(self):
                super().__init__()
                self.channels = []
                self.in_card = False
                self.current_tag = None
                self.current_data = {}

            def handle_starttag(self, tag, attrs):
                attrs_dict = dict(attrs)
                if tag == 'a' and 'card' in attrs_dict.get('class', ''):
                    self.in_card = True
                    self.current_data = {
                        'id': attrs_dict.get('href', '').split('=')[-1] if '=' in attrs_dict.get('href', '') else '',
                        'name': '',
                        'manifest_url': f"{DLHD_API_BASE}{attrs_dict.get('href', '')}",
                        'source': 'unknown',
                        'status': 'online',
                        'category': 'Other'
                    }
                elif self.in_card and tag == 'div':
                    class_value = attrs_dict.get('class', '')
                    if 'card__title' in class_value:
                        self.current_tag = 'title'
                    elif class_value == '':
                        self.current_tag = 'id_div'

            def handle_endtag(self, tag):
                if tag == 'a' and self.in_card:
                    if not self.current_data.get('name'):
                        self.current_data['name'] = 'Unknown'
                    self.channels.append(self.current_data)
                    self.in_card = False
                    self.current_tag = None
                    self.current_data = {}
                elif tag == 'div':
                    self.current_tag = None

            def handle_data(self, data):
                if self.in_card:
                    if self.current_tag == 'title':
                        self.current_data['name'] += data.strip()
                    elif self.current_tag == 'id_div' and data.strip().startswith('ID:'):
                        id_part = data.strip().split(':')[1].strip() if ':' in data.strip() else ''
                        if id_part:
                            self.current_data['id'] = id_part

        parser = ChannelParser()
        parser.feed(r.text)
        return parser.channels

    def fetch_stream_url(self, manifest_url: str) -> tuple[str | None, str]:
        """Resolve a channel's manifest URL down to a playable stream URL.

        Two-stage flow:
          1. `manifest_url` is treated as a *watch* page. Fetch it and look
             for the iframe pointing at the real embed page (stream-XXX.php).
             If nothing matches, fall back to treating manifest_url itself
             as the embed page.
          2. Fetch that embed page. If it wraps another player behind a
             nested iframe, follow that too and use the nested page as the
             Referer for playback.

        Returns (stream_url_or_None, referer_to_use_for_playback).
        """
        # --- Stage 1: watch page -> embed page ---
        embed_url = manifest_url
        try:
            r0 = self._get_with_retry(manifest_url)
            r0.raise_for_status()
            watch_html = r0.text

            embed_match = re.search(
                r'<iframe[^>]+src=["\'](https?://dlhd\.st/stream/stream-[^"\']+\.php)["\']',
                watch_html, re.IGNORECASE,
            )
            if not embed_match:
                embed_match = re.search(
                    r'<iframe[^>]+src=["\'](https?://dlhd\.st/[^"\']+)["\']',
                    watch_html, re.IGNORECASE,
                )
            if embed_match:
                embed_url = embed_match.group(1)
        except Exception:
            pass  # manifest_url may already *be* the embed page; carry on

        # --- Stage 2: embed page -> nested player page ---
        r = self._get_with_retry(embed_url)
        r.raise_for_status()
        html = r.text
        referer = embed_url

        html, referer = _follow_nested_iframe(self._get_with_retry, html, embed_url)

        stream_url = _extract_stream_from_html(html)
        if stream_url:
            return stream_url, referer

        # dlhd-specific fallbacks
        m = re.search(r'/embed/([^/]+)', manifest_url)
        if m:
            return f"{DLHD_API_BASE}/track/{m.group(1)}", referer
        m = re.search(r'/watch\.php\?id=(\d+)', manifest_url)
        if m:
            return f"{DLHD_API_BASE}/stream/stream-{m.group(1)}.php", referer

        return None, referer


@dataclass
class DLHDChannel:
    id: str
    name: str
    category: str
    status: str
    manifest_url: str
    source: str
    country: str | None = None

    @classmethod
    def from_raw(cls, raw: dict[str, Any]) -> "DLHDChannel":
        return cls(
            id=str(raw.get("id") or ""),
            name=str(raw.get("name") or "Unknown"),
            category=str(raw.get("category") or "Other"),
            status=str(raw.get("status") or "online"),
            manifest_url=str(raw.get("manifest_url") or ""),
            source=str(raw.get("source") or "unknown"),
            country=raw.get("country"),
        )


def _dlhd_column_widths(width: int) -> tuple[int, int, int, int]:
    overhead = 40
    rem = width - overhead
    if rem < 20:
        name_w = max(15, rem)
        cat_w = 0
    else:
        cat_w = min(15, max(10, int(rem * 0.25)))
        name_w = rem - cat_w
    return name_w, 12, 12, cat_w


def _dlhd_channel_row(ch: DLHDChannel, name_w: int, src_w: int, country_w: int, cat_w: int, c: C) -> str:
    badge = f"{c.sage}{c.bold}● ON {c.reset}" if ch.status == "online" else f"{c.rose}{c.bold}○ OFF{c.reset}"

    disp_name = truncate_str(ch.name, name_w)
    name_str = f"{c.bold}{disp_name}{c.reset}"

    disp_cat = truncate_str(ch.category, cat_w) if cat_w > 0 else ""
    cat_str = f"{c.slate}{disp_cat}{c.reset}"

    disp_src = truncate_str(ch.source, src_w)
    src_str = f"{c.dim}{disp_src}{c.reset}"

    disp_country = truncate_str(ch.country or "—", country_w)
    country_str = f"{c.dim}{disp_country}{c.reset}"

    return f"{badge}  {name_str}  {cat_str}  {src_str}  {country_str}"


def _dlhd_find_channel(channels: list[DLHDChannel], selector: str) -> DLHDChannel | None:
    for ch in channels:
        if ch.id == selector:
            return ch
    selector_l = selector.lower()
    matches = [ch for ch in channels if selector_l in ch.name.lower()]
    if len(matches) == 1:
        return matches[0]
    if len(matches) > 1:
        for ch in matches:
            if ch.name.lower() == selector_l:
                return ch
    return None


def _dlhd_print_details(ch: DLHDChannel, stream_url: str | None, c: C, referer: str | None = None) -> None:
    print(f"\n  {c.sky}┌──{c.reset} {c.bold}CHANNEL DETAILS{c.reset} {c.sky}{'─' * 50}┐{c.reset}")
    print(f"  {c.sky}│{c.reset}  {c.bold}Name:{c.reset}      {c.bold}{ch.name}{c.reset}")
    print(f"  {c.sky}│{c.reset}  {c.bold}Category:{c.reset}  {ch.category}")
    print(f"  {c.sky}│{c.reset}  {c.bold}Source:{c.reset}    {ch.source} ({ch.status})")
    print(f"  {c.sky}│{c.reset}  {c.bold}Embed URL:{c.reset} {c.sky}{ch.manifest_url}{c.reset}")

    if stream_url:
        effective_referer = referer or ch.manifest_url
        origin = f"{urllib.parse.urlparse(effective_referer).scheme}://{urllib.parse.urlparse(effective_referer).netloc}"
        print(f"  {c.sky}│{c.reset}  {c.bold}M3U8 URL:{c.reset}  {c.sage}{stream_url}{c.reset}")
        print(f"  {c.sky}│{c.reset}")
        print(f"  {c.sky}│{c.reset}  {c.bold}To play with mpv:{c.reset}")
        print(
            f"  {c.sky}│{c.reset}  mpv \"{stream_url}\" "
            f"--http-header-fields=\"Referer: {effective_referer},Origin: {origin}\" "
            f"--no-cache --cache-secs=10"
        )
    else:
        print(f"  {c.sky}│{c.reset}  {c.rose}Failed to decrypt stream M3U8 url.{c.reset}")

    print(f"  {c.sky}└────────────────────────────────────────────────────────────────────┘{c.reset}\n")


def _dlhd_play_channel(
    client: DaddyLiveClient,
    chosen: DLHDChannel,
    play_only: bool,
    c: C,
    interactive: bool = True,
) -> int | None:
    """Handle one selected channel.

    Returns an exit code to stop, or None to go back to the channel list.
    """
    print(f"\n  {c.bold}Selected:{c.reset} {c.sky}{chosen.name}{c.reset}")

    try:
        stream_url, stream_referer = fetch_with_spinner(
            f"Decrypting stream URL for \"{chosen.name}\"",
            lambda: client.fetch_stream_url(chosen.manifest_url),
            c,
        )
    except Exception as e:
        sys.stderr.write(f"{c.rose}✗ Failed to fetch stream details: {e}{c.reset}\n")
        return 1

    if play_only:
        if stream_url and is_valid_url(stream_url):
            print(stream_url)
            return 0
        sys.stderr.write(f"{c.rose}✗ Could not resolve a stream URL for \"{chosen.name}\"{c.reset}\n")
        return 1

    if not stream_url:
        _dlhd_print_details(chosen, stream_url, c, referer=stream_referer)
        if not interactive:
            return 1
        pause(c, "Press Enter to return to the channel list...")
        return None

    while True:
        action = choose_playback_action(c, allow_mpv=True, back_label="Back to channel list")
        if action in (None, "back"):
            return None
        if action == "mpv":
            play_with_mpv(stream_url, c, referer=stream_referer)
            return None
        if action == "browser":
            open_in_browser(chosen.manifest_url, c)
        elif action == "details":
            _dlhd_print_details(chosen, stream_url, c, referer=stream_referer)
            pause(c)


def run_dlhd(use_color: bool, play_only: bool = False, channel_selector: str | None = None) -> int:
    c = C(use_color)

    with DaddyLiveClient() as client:
        try:
            channels_raw = fetch_with_spinner("Fetching TV channels list", client.fetch_channels, c)
        except Exception as e:
            sys.stderr.write(f"{c.rose}✗ Failed to fetch channels: {e}{c.reset}\n")
            return 1

        channels = [DLHDChannel.from_raw(raw) for raw in channels_raw]
        if not channels:
            sys.stderr.write(f"{c.rose}✗ No channels returned from API{c.reset}\n")
            return 1

        print_banner("DaddyLive TV Channels", "https://dlhd.st/", c)

        name_w, src_w, country_w, cat_w = _dlhd_column_widths(_term_width() - 8)

        hdr_status = "STATUS".ljust(5)
        hdr_name = "CHANNEL NAME".ljust(name_w)
        hdr_category = "CATEGORY".ljust(cat_w) if cat_w > 0 else ""
        hdr_source = "SOURCE".ljust(src_w)
        hdr_country = "COUNTRY".ljust(country_w)

        header_row = (
            f"{c.bold}{c.slate}"
            f"{hdr_status}  {hdr_name}  {hdr_category}  {hdr_source}  {hdr_country}"
            f"{c.reset}"
        )

        channels.sort(key=lambda x: (x.status != "online", x.category, x.name))
        rows = [_dlhd_channel_row(ch, name_w, src_w, country_w, cat_w, c) for ch in channels]

        if channel_selector is not None:
            chosen = _dlhd_find_channel(channels, channel_selector)
            if chosen is None:
                sys.stderr.write(
                    f"{c.rose}✗ No channel matched {channel_selector!r} "
                    f"(use exact id, or a name substring that matches exactly one channel){c.reset}\n"
                )
                return 1
            code = _dlhd_play_channel(client, chosen, play_only, c, interactive=False)
            return 0 if code is None else code

        while True:
            idx = pick_from_list(
                f"Select a TV channel  {c.dim}({len(channels)} channels){c.reset}",
                rows,
                c=c,
                header_row=header_row,
            )
            if idx is None:
                print(f"\n{c.slate}  cancelled.{c.reset}")
                return 0

            code = _dlhd_play_channel(client, channels[idx], play_only, c, interactive=True)
            if code is not None:
                return code


# =========================================================================
# Source 2 — BINTV (bintv.cc)
# =========================================================================

BIN_BASE_URL = "https://www.bintv.cc"
BIN_PAGE_TIMEOUT = 30000  # ms for page load
BIN_ONCLICK_PATTERN = re.compile(
    r"handleMatchClick\(\s*({.+?})\s*\)",
    re.DOTALL,
)


def _load_playwright():
    try:
        from playwright.sync_api import sync_playwright, TimeoutError as PlaywrightTimeout
    except ImportError:
        sys.stderr.write("error: the 'bintv' source needs playwright.\n")
        sys.stderr.write("       install with: pip install playwright\n")
        sys.stderr.write("       then run:  playwright install chromium\n")
        sys.exit(2)
    return sync_playwright, PlaywrightTimeout


@dataclass
class BINStream:
    source_name: str
    url: str
    is_m3u8: bool = False
    is_proxy: bool = False

    def __post_init__(self) -> None:
        self.is_proxy = "noooooads" in self.url
        direct = self.direct_url
        self.is_m3u8 = self.url.endswith(".m3u8") or direct.endswith(".m3u8")

    @property
    def direct_url(self) -> str:
        """Extract the actual stream URL from behind the proxy."""
        if not self.is_proxy:
            return self.url
        parsed = urlparse(self.url)
        params = parse_qs(parsed.query)
        if "src" in params:
            return params["src"][0]
        return self.url


@dataclass
class BINEvent:
    title: str
    category: str
    date: int  # Unix timestamp (ms)
    status: str  # "Live" or empty
    poster: str | None
    sources: list[BINStream] = field(default_factory=list)
    viewers: int = 0
    ends_at: int = 0

    @property
    def is_live(self) -> bool:
        return self.status == "Live"

    @property
    def timestamp_sec(self) -> int:
        return self.date // 1000 if self.date else 0

    @classmethod
    def from_json(cls, data: dict) -> "BINEvent":
        sources = [
            BINStream(source_name=src.get("source", "Unknown"), url=src.get("url", ""))
            for src in data.get("sources", [])
        ]
        return cls(
            title=data.get("title", "?"),
            category=data.get("category", "Unknown"),
            date=data.get("date", 0),
            status=data.get("status", ""),
            poster=data.get("poster"),
            sources=sources,
            viewers=data.get("viewers", 0),
            ends_at=data.get("endsAt", 0),
        )


def fetch_bin_events() -> list[BINEvent]:
    """Use Playwright to load the page and extract event data from onclick handlers."""
    sync_playwright, PlaywrightTimeout = _load_playwright()

    events: list[BINEvent] = []
    seen: set[str] = set()

    with sync_playwright() as p:
        browser = p.chromium.launch(headless=True)
        page = browser.new_page(
            user_agent=(
                "Mozilla/5.0 (X11; Linux x86_64) AppleWebKit/537.36 "
                "(KHTML, like Gecko) Chrome/131.0.0.0 Safari/537.36"
            )
        )

        try:
            page.goto(BIN_BASE_URL, wait_until="domcontentloaded", timeout=BIN_PAGE_TIMEOUT)
            page.wait_for_timeout(3000)

            onclick_data = page.evaluate(
                """
                () => {
                    return [...document.querySelectorAll('[onclick]')]
                        .map(el => el.getAttribute('onclick'))
                        .filter(onclick => onclick && onclick.includes('handleMatchClick'));
                }
                """
            )

            for onclick in onclick_data:
                match = BIN_ONCLICK_PATTERN.search(onclick)
                if not match:
                    continue
                try:
                    data = json.loads(match.group(1))
                except json.JSONDecodeError:
                    continue

                title = data.get("title", "")
                if not title or title in seen:
                    continue

                seen.add(title)
                events.append(BINEvent.from_json(data))

        except PlaywrightTimeout:
            raise RuntimeError(f"Page load timed out after {BIN_PAGE_TIMEOUT}ms")
        finally:
            browser.close()

    return events


def _bin_format_time(timestamp_ms: int) -> tuple[str, str]:
    if not timestamp_ms:
        return "—", "scheduled"
    ts = timestamp_ms // 1000
    now = int(time.time())
    if ts <= now:
        state = "live"
    elif ts - now < 86400:
        state = "soon"
    else:
        state = "scheduled"
    txt = time.strftime("%b %d %I:%M %p %Z", time.localtime(ts)).strip()
    return txt, state


def _bin_column_widths(width: int) -> tuple[int, int, int]:
    overhead = 35
    rem = width - overhead
    if rem < 20:
        return max(20, rem), 0, 15
    cat_w = min(15, max(10, int(rem * 0.2)))
    time_w = 18
    name_w = rem - cat_w - time_w
    return name_w, cat_w, time_w


def _bin_event_row(ev: BINEvent, name_w: int, cat_w: int, time_w: int, c: C) -> str:
    when, state = _bin_format_time(ev.date)

    if ev.is_live:
        badge = f"{c.warn}{c.bold}●LIVE{c.reset}"
    elif state == "soon":
        badge = f"{c.amber}SOON {c.reset}"
    else:
        badge = f"{c.dim}SCHED{c.reset}"

    time_color = {
        "live": c.warn,
        "soon": c.amber,
        "scheduled": c.slate,
    }.get(state, c.slate)

    disp_name = truncate_str(ev.title, name_w)
    disp_cat = truncate_str(ev.category, cat_w) if cat_w > 0 else ""
    disp_time = truncate_str(when, time_w)

    return (
        f"{badge}  "
        f"{c.bold}{disp_name}{c.reset}  "
        f"{c.dim}{disp_cat}{c.reset}  "
        f"{time_color}{disp_time}{c.reset}"
    )


def _bin_stream_row(stream: BINStream, c: C) -> str:
    type_badge = f"{c.sage}M3U8{c.reset}" if stream.is_m3u8 else f"{c.sky}LINK{c.reset}"
    proxy_badge = f" {c.dim}(proxy){c.reset}" if stream.is_proxy else ""
    return f" {type_badge}  {c.bold}{stream.source_name}{c.reset}{proxy_badge}"


def _bin_print_details(stream: BINStream, event_title: str, c: C) -> None:
    type_badge = (
        f"{c.sage}{c.bold}★ M3U8{c.reset}"
        if stream.is_m3u8
        else f"{c.sky}{c.bold}▶ LINK{c.reset}"
    )

    print(f"\n{c.sky}┌──{c.reset} {c.bold}STREAM DETAILS{c.reset} {c.sky}{'─' * 50}┐{c.reset}")
    print(f"  {c.sky}│{c.reset}  {c.bold}Event:{c.reset}  {c.bold}{event_title}{c.reset}")
    print(f"  {c.sky}│{c.reset}  {c.bold}Source:{c.reset} {type_badge} {c.bold}{stream.source_name}{c.reset}")
    print(f"  {c.sky}│{c.reset}  {c.bold}URL:{c.reset}")

    url = stream.direct_url
    wrap_width = max(20, _term_width() - 14)

    while url:
        chunk = url[:wrap_width]
        url = url[wrap_width:]
        print(f"  {c.sky}│{c.reset}    {c.sky}{chunk}{c.reset}")

    if stream.is_proxy:
        print(f"  {c.sky}│{c.reset}  {c.bold}Proxy:{c.reset} {c.dim}{stream.url}{c.reset}")

    print(f"  {c.sky}└────────────────────────────────────────────────────────────────────┘{c.reset}\n")


def run_bintv(
    use_color: bool,
    category_filter: str | None = None,
    live_only: bool = False,
    list_mode: bool = False,
    json_output: bool = False,
) -> int:
    c = C(use_color)

    if not json_output:
        print_banner("BINTV.cc  Streams", BIN_BASE_URL, c)

    try:
        events = fetch_with_spinner("fetching events", fetch_bin_events, c, quiet=json_output)
    except Exception as e:
        sys.stderr.write(f"{c.rose}✗  {e}{c.reset}\n")
        return 1

    if not events:
        sys.stderr.write(f"{c.rose}✗  no events found{c.reset}\n")
        return 1

    # Filters
    if category_filter:
        events = [e for e in events if e.category.lower() == category_filter.lower()]

    if live_only:
        now = int(time.time())
        events = [
            e
            for e in events
            if e.is_live or (e.timestamp_sec and e.timestamp_sec <= now)
        ]

    if not events:
        sys.stderr.write(f"{c.rose}✗  no events match the filter{c.reset}\n")
        return 1

    events.sort(key=lambda e: (not e.is_live, e.date or 0))

    # JSON mode
    if json_output:
        output = [
            {
                "title": ev.title,
                "category": ev.category,
                "date": ev.date,
                "is_live": ev.is_live,
                "streams": [
                    {
                        "source": s.source_name,
                        "url": s.direct_url,
                        "proxy_url": s.url,
                        "is_m3u8": s.is_m3u8,
                    }
                    for s in ev.sources
                ],
            }
            for ev in events
        ]
        print(json.dumps(output, indent=2))
        return 0

    # List mode
    if list_mode:
        for ev in events:
            when, state = _bin_format_time(ev.date)
            badge = (
                "●LIVE"
                if ev.is_live or state == "live"
                else "SOON"
                if state == "soon"
                else "SCHED"
            )
            print(f"\n{badge}  {ev.title}")
            print(f"  Category: {ev.category}  |  Time: {when}")
            for s in ev.sources:
                type_str = "[M3U8]" if s.is_m3u8 else "[LINK]"
                proxy_str = " (via proxy)" if s.is_proxy else ""
                print(f"    {type_str} {s.source_name}{proxy_str}: {s.direct_url}")
        return 0

    # Interactive
    if not sys.stdout.isatty():
        sys.stderr.write(
            "note: interactive mode requires TTY; use --list or --json for scripted output\n"
        )
        return 1

    name_w, cat_w, time_w = _bin_column_widths(_term_width() - 4)

    hdr_status = "STATUS".ljust(5)
    hdr_name = "EVENT".ljust(name_w)
    hdr_category = "CATEGORY".ljust(cat_w) if cat_w > 0 else ""
    hdr_time = "TIME".ljust(time_w)

    header_row = (
        f"{c.bold}{c.slate}"
        f"{hdr_status}  {hdr_name}  {hdr_category}  {hdr_time}"
        f"{c.reset}"
    )

    rows = [_bin_event_row(e, name_w, cat_w, time_w, c) for e in events]

    # ── event picker loop ─────────────────────────────────────────────
    while True:
        idx = pick_from_list(
            f"Select an event  {c.dim}({len(events)} available){c.reset}",
            rows,
            c=c,
            header_row=header_row,
        )
        if idx is None:
            print(f"\n{c.slate}  cancelled.{c.reset}")
            return 0

        chosen = events[idx]

        print(f"\n{c.bold}Event:{c.reset} {c.sky}{chosen.title}{c.reset}")
        print(f"  {c.bold}Category:{c.reset} {c.dim}{chosen.category}{c.reset}")

        if not chosen.sources:
            sys.stderr.write(f"{c.rose}✗  no streams available{c.reset}\n")
            pause(c, "Press Enter to return to the event list...")
            continue

        # ── stream picker loop ────────────────────────────────────────
        while True:
            rows2 = [_bin_stream_row(s, c) for s in chosen.sources]

            idx2 = pick_from_list(
                f"Select a stream  {c.dim}({len(chosen.sources)} available){c.reset}",
                rows2,
                c=c,
            )
            if idx2 is None:
                break  # back to event list

            stream = chosen.sources[idx2]
            print(f"\n{c.bold}Source:{c.reset} {c.sky}{stream.source_name}{c.reset}")

            back_to_event_list = False

            # ── playback action loop ──────────────────────────────────
            while True:
                action = choose_playback_action(c, allow_mpv=False, back_label="Back to channel list")

                if action is None:
                    break  # back to stream list

                if action == "browser":
                    target_url = stream.direct_url
                    if not is_valid_url(target_url):
                        target_url = stream.url
                    open_in_browser(target_url, c)

                elif action == "details":
                    _bin_print_details(stream, chosen.title, c)
                    pause(c)

                elif action == "back":
                    back_to_event_list = True
                    break

            if back_to_event_list:
                break

    return 0


# =========================================================================
# Source 3 — PPV (ppv.st)
# =========================================================================

PPV_DEFAULT_API_BASE = "https://api.ppv.st/api"
PPV_ALT_API_BASES = (
    "https://api.ppv.tj/api",
    "https://api.ppvs.pk/api",
    "https://api.ppv.rw/api",
    "https://api.ppv.ms/api",
    "https://api.ppv.bi/api",
    "https://api.ppv.ug/api",
)
PPV_API_DOMAINS = ("ppv.st", "ppv.tj", "ppvs.pk", "ppv.rw", "ppv.ms", "ppv.bi", "ppv.ug")
PPV_USER_AGENT = "ppv_picker/1.0 (+https://ppv.st) curl/8"


class _PPVAllBasesFailed(RuntimeError):
    """Raised when every API base in the failover chain errors out."""

    def __init__(self, attempted: list[str], last_error: str):
        super().__init__(
            f"all {len(attempted)} API base(s) failed; last error: {last_error}"
        )
        self.attempted = attempted
        self.last_error = last_error


def _ppv_build_api_chain(requested_base: str) -> list[str]:
    """Return an ordered list of API bases to try."""
    seen: set[str] = set()
    chain: list[str] = []

    def add(b: str) -> None:
        b = b.rstrip("/")
        if b and b not in seen:
            seen.add(b)
            chain.append(b)

    add(requested_base or PPV_DEFAULT_API_BASE)

    for alt in PPV_ALT_API_BASES:
        add(alt)

    for d in PPV_API_DOMAINS:
        add(f"https://api.{d}/api")

    return chain


def _recover_uri_from_iframe(iframe_url: str) -> str:
    if not iframe_url:
        return ""
    return re.sub(r"^https?://[^/]+/embed/", "", iframe_url)


@dataclass
class PPVEmbed:
    label: str
    uri: str | None
    locale: str | None
    iframe_url: str
    is_default: bool = False

    def ppv_url(self, host: str = "ppv.st", event_uri: str | None = None) -> str:
        """Best-effort shareable URL."""
        tail = ""

        if self.uri:
            tail = self.uri
            if event_uri and not tail.startswith(event_uri):
                tail = f"{event_uri.rstrip('/')}/{tail.lstrip('/')}"
        elif self.iframe_url:
            tail = _recover_uri_from_iframe(self.iframe_url)

        return f"https://{host}/live/{tail}" if tail else f"https://{host}/"


class PPVClient:
    def __init__(
        self,
        api_base: str = PPV_DEFAULT_API_BASE,
        client: httpx.Client | None = None,
        api_chain: list[str] | None = None,
    ):
        _require_httpx()
        self.api_chain = list(api_chain) if api_chain else _ppv_build_api_chain(api_base)
        self.api_base = self.api_chain[0]

        own_client = client is None
        self.client = client or httpx.Client(
            headers={
                "User-Agent": PPV_USER_AGENT,
                "Origin": "https://ppv.st",
                "Referer": "https://ppv.st/",
                "Accept": "application/json",
            },
            timeout=TIMEOUT,
            follow_redirects=True,
        )
        self._owns_client = own_client

    def close(self) -> None:
        if self._owns_client and self.client is not None:
            self.client.close()

    def __enter__(self) -> "PPVClient":
        return self

    def __exit__(self, *exc) -> None:
        self.close()

    # ---------- failover plumbing ----------

    @staticmethod
    def _unrecoverable(exc: BaseException) -> bool:
        """
        A direct LookupError means a real 'not found' result; do not failover
        past it. KeyError/IndexError are treated as malformed responses and
        are failover-eligible.
        """
        return type(exc) is LookupError

    def _with_failover(self, call) -> tuple[Any, str]:
        """Try call(self.client, base) against each base in api_chain in order."""
        attempted: list[str] = []
        last_err: BaseException | None = None

        for base in self.api_chain:
            attempted.append(base)
            self.api_base = base

            try:
                result = call(self.client, base)
                return result, base
            except Exception as e:
                if self._unrecoverable(e):
                    raise
                last_err = e
                continue

        raise _PPVAllBasesFailed(
            attempted=attempted,
            last_error=repr(last_err) if last_err else "unknown",
        )

    # ---------- endpoints ----------

    def index(self) -> list[dict[str, Any]]:
        """Returns the flat streams list from /api/streams."""

        def call(client: httpx.Client, base: str) -> list[dict[str, Any]]:
            r = client.get(f"{base}/streams")
            r.raise_for_status()

            d = r.json()
            if not d.get("success"):
                raise RuntimeError(f"index: server returned success=false: {d}")

            return d.get("streams") or []

        result, _ = self._with_failover(call)
        return result

    def event(self, uri_path: str) -> dict[str, Any]:
        """Returns the data object from /api/streams/<uri-path>."""

        def call(client: httpx.Client, base: str) -> dict[str, Any]:
            r = client.get(f"{base}/streams/{uri_path}")

            if r.status_code == 404:
                raise LookupError(f"event: not found: {uri_path}")

            r.raise_for_status()

            d = r.json()
            if not d.get("success"):
                s = d.get("statusCode") or d.get("status_code")
                if s == 404:
                    raise LookupError(f"event: not found: {uri_path}")
                raise RuntimeError(f"event: server returned success=false: {d}")

            return d["data"]

        result, _ = self._with_failover(call)
        return result


@dataclass
class PPVEvent:
    id: int
    name: str
    tag: str | None
    source_tag: str | None
    locale: str | None
    category_name: str | None
    uri: str
    poster: str | None
    starts_at: int
    ends_at: int
    viewers: int
    always_live: bool
    iframe: str | None
    substreams: list[dict] = field(default_factory=list)

    @classmethod
    def from_index(cls, cat_name: str, raw: dict) -> "PPVEvent":
        return cls(
            id=int(raw.get("id") or 0),
            name=str(raw.get("name") or "?"),
            tag=raw.get("tag"),
            source_tag=raw.get("source_tag"),
            locale=raw.get("locale"),
            category_name=cat_name,
            uri=str(raw.get("uri_name") or ""),
            poster=raw.get("poster"),
            starts_at=int(raw.get("starts_at") or 0),
            ends_at=int(raw.get("ends_at") or 0),
            viewers=int(raw.get("viewers") or 0),
            always_live=bool(raw.get("always_live")),
            iframe=raw.get("iframe"),
            substreams=list(raw.get("substreams") or []),
        )

    @classmethod
    def from_event(cls, raw: dict) -> "PPVEvent":
        """Newer events may not be in the index yet — use event endpoint as primary."""
        cat = raw.get("category_name") or "(?)"
        starts = int(raw.get("start_timestamp") or raw.get("starts_at") or 0)
        ends = int(raw.get("end_timestamp") or raw.get("ends_at") or 0)

        return cls(
            id=int(raw.get("id") or 0),
            name=str(raw.get("name") or "?"),
            tag=raw.get("tag"),
            source_tag=raw.get("source_tag"),
            locale=raw.get("locale"),
            category_name=cat,
            uri=str(raw.get("uri") or raw.get("uri_name") or ""),
            poster=raw.get("poster"),
            starts_at=starts,
            ends_at=ends,
            viewers=int(raw.get("viewers") or 0),
            always_live=bool(raw.get("always_live", raw.get("always_live_feed"))),
            iframe=raw.get("iframe") or raw.get("default_iframe"),
            substreams=list(raw.get("substreams") or []),
        )

    def embeds(self, default_iframe: str | None = None) -> list[PPVEmbed]:
        out: list[PPVEmbed] = []

        dflt = default_iframe or self.iframe
        if dflt:
            out.append(
                PPVEmbed(
                    label=f"{self.source_tag or 'Default'} (default)",
                    uri=None,
                    locale=self.locale,
                    iframe_url=dflt,
                    is_default=True,
                )
            )

        for sub in self.substreams:
            uri = sub.get("uri") or ""
            if not uri:
                uri = _recover_uri_from_iframe(sub.get("iframe") or "")

            out.append(
                PPVEmbed(
                    label=sub.get("source_tag") or uri or "Stream",
                    uri=uri,
                    locale=sub.get("locale"),
                    iframe_url=sub.get("iframe") or "",
                    is_default=False,
                )
            )

        return out


def _ppv_format_start(unix_ts: int, ends_at: int = 0) -> tuple[str, str]:
    if not unix_ts:
        return "—", "info"

    now = int(time.time())

    if ends_at and ends_at < now:
        state = "ended"
    elif unix_ts <= now:
        state = "live"
    elif unix_ts - now < 86400:
        state = "soon"
    else:
        state = "info"

    txt = time.strftime("%b %d %I:%M %p %Z", time.localtime(unix_ts)).strip()
    return txt, state


def _ppv_column_widths(width: int) -> tuple[int, int, int, int]:
    overhead = 47
    rem = width - overhead
    if rem < 20:
        name_w = max(15, rem)
        cat_w = 0
    else:
        cat_w = min(20, max(10, int(rem * 0.25)))
        name_w = rem - cat_w
    return name_w, 15, 19, cat_w


def _ppv_event_row(ev: PPVEvent, name_w: int, src_w: int, time_w: int, cat_w: int, c: C) -> str:
    when, state = _ppv_format_start(ev.starts_at, ev.ends_at)

    if ev.always_live:
        badge = f"{c.sage}{c.bold}24/7 {c.reset}"
    elif state == "live":
        badge = f"{c.warn}{c.bold}●LIVE{c.reset}"
    elif state == "soon":
        badge = f"{c.amber}SOON {c.reset}"
    elif state == "ended":
        badge = f"{c.dim}DONE {c.reset}"
    else:
        badge = "     "

    time_color = {
        "live": c.warn,
        "soon": c.amber,
        "ended": c.dim,
        "info": c.slate,
    }.get(state, c.slate)

    disp_name = truncate_str(ev.name, name_w)
    name_str = f"{c.bold}{disp_name}{c.reset}"

    disp_src = truncate_str(ev.source_tag or "", src_w)
    src_str = f"{c.slate}{disp_src}{c.reset}"

    disp_time = truncate_str(when, time_w)
    time_str = f"{time_color}{disp_time}{c.reset}"

    disp_cat = truncate_str(ev.category_name or "", cat_w) if cat_w > 0 else ""
    cat_str = f"{c.dim}{disp_cat}{c.reset}"

    return f"{badge}  {name_str}  {src_str}  {time_str}  {cat_str}"


def _ppv_embed_row(emb: PPVEmbed, c: C) -> str:
    if emb.is_default:
        marker = f"{c.sage}{c.bold}★{c.reset}"
        suffix = f"  {c.dim}(default){c.reset}"
    else:
        marker = f"{c.slate}◦{c.reset}"
        suffix = ""

    label = f"{c.bold}{emb.label}{c.reset}"
    loc = f"  {c.dim}{emb.locale}{c.reset}" if emb.locale else ""

    return f" {marker}  {label}{loc}{suffix}"


def _ppv_print_embed(emb: PPVEmbed, ppv_host: str, event_uri: str | None, c: C) -> None:
    badge = (
        f"{c.sage}{c.bold}★ default{c.reset}"
        if emb.is_default
        else f"{c.sky}▶ substream{c.reset}"
    )
    loc = f" {c.dim}[{emb.locale}]{c.reset}" if emb.locale else ""
    ppv_url = emb.ppv_url(ppv_host, event_uri)

    print(f"\n{c.sky}┌──{c.reset} {c.bold}STREAM DETAILS{c.reset} {c.sky}{'─' * 50}┐{c.reset}")
    print(f"  {c.sky}│{c.reset}  {c.bold}Source:{c.reset}   {badge}{loc} {c.bold}{emb.label}{c.reset}")
    print(f"  {c.sky}│{c.reset}  {c.bold}PPV URL:{c.reset}  {c.sky}{ppv_url}{c.reset}")
    print(f"  {c.sky}│{c.reset}  {c.bold}Embed:{c.reset}    {c.sky}{emb.iframe_url}{c.reset}")
    print(f"  {c.sky}└────────────────────────────────────────────────────────────────────┘{c.reset}\n")


def derive_ppv_host(api_base: str) -> str:
    for d in PPV_API_DOMAINS:
        if d in api_base:
            return d
    return "ppv.st"


def run_ppv(use_color: bool, api_base: str, show_default: bool) -> int:
    c = C(use_color)
    ppv_host = derive_ppv_host(api_base)
    chain = _ppv_build_api_chain(api_base)

    print_banner("ppv.st  Stream Links", chain[0], c)

    with PPVClient(api_base=api_base) as client:
        # ── fetch event index ────────────────────────────────────────────
        try:
            index = fetch_with_spinner(
                f"Fetching event index [{client.api_base}]",
                client.index,
                c,
            )
        except _PPVAllBasesFailed as e:
            sys.stderr.write(
                f"\n{c.rose}✗  every API base failed ({len(e.attempted)} tried){c.reset}\n"
                f"{c.dim}   last error: {e.last_error}{c.reset}\n"
            )
            return 1
        except Exception as e:
            sys.stderr.write(f"{c.rose}✗  {e}{c.reset}\n")
            return 1

        if client.api_base != chain[0]:
            sys.stderr.write(
                f"  {c.amber}↻{c.reset}  {c.dim}using fallback {client.api_base}{c.reset}\n"
            )

        events: list[PPVEvent] = []

        for cat in index:
            cname = cat.get("category") or cat.get("category_name") or "(?)"
            for raw in cat.get("streams") or []:
                events.append(PPVEvent.from_index(cname, raw))

        if not events:
            sys.stderr.write(f"{c.rose}✗  no events found in index{c.reset}\n")
            return 1

        name_w, src_w, time_w, cat_w = _ppv_column_widths(_term_width() - 4)

        hdr_status = "STATUS".ljust(5)
        hdr_name = "EVENT NAME".ljust(name_w)
        hdr_source = "SOURCE".ljust(src_w)
        hdr_time = "START TIME".ljust(time_w)
        hdr_category = "CATEGORY".ljust(cat_w) if cat_w > 0 else ""

        header_row = (
            f"{c.bold}{c.slate}"
            f"{hdr_status}  {hdr_name}  {hdr_source}  {hdr_time}  {hdr_category}"
            f"{c.reset}"
        )

        events.sort(key=lambda e: (e.always_live, e.starts_at, e.category_name or ""))
        rows = [_ppv_event_row(e, name_w, src_w, time_w, cat_w, c) for e in events]

        # ── event picker loop ─────────────────────────────────────────────
        while True:
            idx = pick_from_list(
                f"Select an event  {c.dim}({len(events)} on offer){c.reset}",
                rows,
                c=c,
                header_row=header_row,
            )
            if idx is None:
                print(f"\n{c.slate}  cancelled.{c.reset}")
                return 0

            chosen = events[idx]

            print(
                f"\n{c.bold}Event:{c.reset} {c.sky}{chosen.name}{c.reset}"
                f"  {c.dim}({chosen.uri}){c.reset}"
            )

            # ── fetch per-event detail ───────────────────────────────────
            detail: dict[str, Any] | None = None

            try:
                detail = fetch_with_spinner(
                    f"Fetching detail for \"{chosen.name}\"",
                    lambda: client.event(chosen.uri),
                    c,
                )
            except LookupError as e:
                sys.stderr.write(f"\n{c.warn}  ⚠  {e}{c.reset}\n")
            except Exception as e:
                sys.stderr.write(f"\n{c.warn}  ⚠  event detail failed: {e}{c.reset}\n")

            if detail:
                fresh = PPVEvent.from_event(detail)

                # Prefer index-provided lists/iframe when present, but keep
                # anything extra the detail endpoint supplied.
                fresh.substreams = chosen.substreams or fresh.substreams
                fresh.iframe = chosen.iframe or fresh.iframe
                chosen = fresh

            embeds = chosen.embeds()

            if not embeds:
                sys.stderr.write(f"{c.rose}✗  no playable sources found{c.reset}\n")
                pause(c, "Press Enter to return to the event list...")
                continue

            if show_default and embeds and embeds[0].is_default:
                print(f"\n{c.sage}↳ default feed (auto-included){c.reset}")
                _ppv_print_embed(embeds[0], ppv_host, chosen.uri, c)

            # ── source picker loop ───────────────────────────────────────
            while True:
                rows2 = [_ppv_embed_row(e, c) for e in embeds]

                idx2 = pick_from_list(
                    f"Select a source  {c.dim}({len(embeds)} available){c.reset}",
                    rows2,
                    c=c,
                )
                if idx2 is None:
                    break  # back to event list

                emb = embeds[idx2]

                print(
                    f"\n{c.bold}Source:{c.reset} {c.sky}{emb.label}{c.reset}"
                    + (f"  {c.dim}[{emb.locale}]{c.reset}" if emb.locale else "")
                )

                back_to_event_list = False

                # ── playback action loop ─────────────────────────────────
                while True:
                    action = choose_playback_action(c, allow_mpv=False, back_label="Back to channel list")

                    if action is None:
                        break  # back to source list

                    if action == "browser":
                        target_url = emb.iframe_url
                        if not is_valid_url(target_url):
                            target_url = emb.ppv_url(ppv_host, chosen.uri)
                        open_in_browser(target_url, c)

                    elif action == "details":
                        _ppv_print_embed(emb, ppv_host, chosen.uri, c)
                        pause(c)

                    elif action == "back":
                        back_to_event_list = True
                        break

                if back_to_event_list:
                    break

    return 0


# =========================================================================
# Source 4 — Streamed (streamed.pk / streamed.st)
# =========================================================================

STREAMED_DEFAULT_BASE = os.environ.get("STREAMED_BASE", "https://streamed.pk").rstrip("/")


class StreamedClient(_HttpRetryClient):
    def __init__(self, base_url: str | None = None, client: httpx.Client | None = None):
        _require_httpx()
        self.base = (base_url or STREAMED_DEFAULT_BASE).rstrip("/")
        client = client or httpx.Client(
            headers={
                "User-Agent": USER_AGENT,
                "Accept": "application/json",
                "Accept-Language": "en-US,en;q=0.9",
                "Accept-Encoding": "gzip, deflate, br",
                "Connection": "keep-alive",
            },
            timeout=TIMEOUT,
            follow_redirects=True,
        )
        super().__init__(client)

    def fetch_sports(self) -> list[dict[str, Any]]:
        r = self._get_with_retry(f"{self.base}/api/sports")
        r.raise_for_status()
        return r.json()

    def fetch_popular_matches(self) -> list[dict[str, Any]]:
        r = self._get_with_retry(f"{self.base}/api/matches/all/popular")
        r.raise_for_status()
        matches = r.json()
        matches.sort(key=lambda m: m.get("date", 0))
        return matches

    def fetch_matches_by_sport(self, sport_id: str) -> list[dict[str, Any]]:
        r = self._get_with_retry(f"{self.base}/api/matches/{sport_id}")
        r.raise_for_status()
        matches = r.json()
        matches.sort(key=lambda m: m.get("date", 0))
        return matches

    def fetch_streams_for_match(self, match: "StreamedMatch") -> list[dict[str, Any]]:
        all_streams: list[dict[str, Any]] = []
        for src in match.sources:
            url = f"{self.base}/api/stream/{src['source']}/{src['id']}"
            try:
                r = self._get_with_retry(url)
                r.raise_for_status()
                all_streams.extend(r.json())
            except Exception:
                continue
        regular = [s for s in all_streams if s.get("source", "").lower() != "admin"]
        admin = [s for s in all_streams if s.get("source", "").lower() == "admin"]
        return regular + admin

    def fetch_stream_url(self, embed_url: str) -> tuple[str | None, str]:
        """Resolve an embed URL down to a playable stream URL."""
        if not embed_url:
            return None, ""

        referer = embed_url
        try:
            r = self._get_with_retry(embed_url)
            r.raise_for_status()
            html = r.text
        except Exception:
            return None, referer

        html, referer = _follow_nested_iframe(self._get_with_retry, html, embed_url)
        return _extract_stream_from_html(html), referer


@dataclass
class StreamedSport:
    id: str
    name: str

    @classmethod
    def from_raw(cls, raw: dict[str, Any]) -> "StreamedSport":
        return cls(
            id=str(raw.get("id") or ""),
            name=str(raw.get("name") or "Unknown"),
        )


@dataclass
class StreamedTeam:
    name: str
    badge: str | None


@dataclass
class StreamedMatch:
    id: str
    title: str
    category: str
    date: int
    poster: str | None
    popular: bool
    teams: dict[str, StreamedTeam | None]
    sources: list[dict[str, str]]
    viewers: int

    @classmethod
    def from_raw(cls, raw: dict[str, Any]) -> "StreamedMatch":
        teams_raw = raw.get("teams") or {}
        home = teams_raw.get("home")
        away = teams_raw.get("away")
        return cls(
            id=str(raw.get("id") or ""),
            title=str(raw.get("title") or "Unknown"),
            category=str(raw.get("category") or "Other"),
            date=int(raw.get("date") or 0),
            poster=raw.get("poster"),
            popular=bool(raw.get("popular")),
            teams={
                "home": StreamedTeam(name=home.get("name", ""), badge=home.get("badge")) if home else None,
                "away": StreamedTeam(name=away.get("name", ""), badge=away.get("badge")) if away else None,
            },
            sources=raw.get("sources") or [],
            viewers=int(raw.get("viewers") or 0),
        )

    def display_title(self) -> str:
        home = self.teams.get("home")
        away = self.teams.get("away")
        if home and away and home.name and away.name:
            return f"{home.name} vs {away.name}"
        return self.title

    def display_time(self) -> str:
        if self.date:
            return datetime.fromtimestamp(self.date / 1000).strftime("%b %d %H:%M")
        return "Unknown time"


@dataclass
class StreamedStream:
    id: str
    stream_no: int
    language: str
    hd: bool
    embed_url: str
    source: str
    viewers: int

    @property
    def is_admin(self) -> bool:
        return self.source.lower() == "admin"

    @classmethod
    def from_raw(cls, raw: dict[str, Any]) -> "StreamedStream":
        return cls(
            id=str(raw.get("id") or ""),
            stream_no=int(raw.get("streamNo") or 0),
            language=str(raw.get("language") or "Unknown"),
            hd=bool(raw.get("hd")),
            embed_url=str(raw.get("embedUrl") or ""),
            source=str(raw.get("source") or "unknown"),
            viewers=int(raw.get("viewers") or 0),
        )


def format_viewers(count: int) -> str:
    if count >= 1_000_000:
        return f"{count/1_000_000:.1f}m".replace(".0m", "m")
    if count >= 1000:
        return f"{count/1000:.1f}k".replace(".0k", "k")
    return str(count)


def _streamed_sport_row(sp: StreamedSport, c: C) -> str:
    return f"{c.bold}{sp.name}{c.reset}"


def _streamed_match_row(mt: StreamedMatch, c: C) -> str:
    when = mt.display_time()
    title = mt.display_title()
    viewers = format_viewers(mt.viewers) if mt.viewers > 0 else ""
    viewers_str = f" {c.dim}({viewers} viewers){c.reset}" if viewers else ""
    return f"{c.slate}{when}{c.reset}  {c.bold}{title}{c.reset}{viewers_str}  {c.dim}({mt.category}){c.reset}"


def _streamed_stream_row(st: StreamedStream, c: C) -> str:
    quality = f"{c.sage}HD{c.reset}" if st.hd else f"{c.dim}SD{c.reset}"
    viewers = format_viewers(st.viewers) if st.viewers > 0 else "0"
    admin_badge = f" {c.rose}[BROWSER ONLY]{c.reset}" if st.is_admin else ""
    return (
        f"#{st.stream_no} {c.bold}{st.language}{c.reset} ({quality}) – "
        f"{c.amber}{st.source}{c.reset} — ({viewers} viewers){admin_badge}"
    )


def _streamed_print_details(st: StreamedStream, stream_url: str | None, c: C, referer: str | None = None) -> None:
    print(f"\n  {c.sky}┌──{c.reset} {c.bold}STREAM DETAILS{c.reset} {c.sky}{'─' * 50}┐{c.reset}")
    print(f"  {c.sky}│{c.reset}  {c.bold}Language:{c.reset}   {st.language}")
    print(f"  {c.sky}│{c.reset}  {c.bold}Quality:{c.reset}    {'HD' if st.hd else 'SD'}")
    print(f"  {c.sky}│{c.reset}  {c.bold}Source:{c.reset}     {st.source}")
    print(f"  {c.sky}│{c.reset}  {c.bold}Embed URL:{c.reset} {c.sky}{st.embed_url}{c.reset}")

    if stream_url:
        effective_referer = referer or st.embed_url
        origin = f"{urllib.parse.urlparse(effective_referer).scheme}://{urllib.parse.urlparse(effective_referer).netloc}"
        print(f"  {c.sky}│{c.reset}  {c.bold}M3U8 URL:{c.reset}  {c.sage}{stream_url}{c.reset}")
        print(f"  {c.sky}│{c.reset}")
        print(f"  {c.sky}│{c.reset}  {c.bold}To play with mpv:{c.reset}")
        print(
            f"  {c.sky}│{c.reset}  mpv \"{stream_url}\" "
            f"--http-header-fields=\"Referer: {effective_referer},Origin: {origin}\" "
            f"--user-agent=\"{USER_AGENT}\""
        )
    else:
        print(f"  {c.sky}│{c.reset}  {c.rose}Could not resolve a direct M3U8 URL.{c.reset}")
        if st.is_admin:
            print(f"  {c.sky}│{c.reset}  {c.warn}Admin streams require a browser due to heavy obfuscation.{c.reset}")

    print(f"  {c.sky}└────────────────────────────────────────────────────────────────────┘{c.reset}\n")


def run_streamed(use_color: bool, play_only: bool = False, base_url: str | None = None) -> int:
    c = C(use_color)
    base = (base_url or STREAMED_DEFAULT_BASE).rstrip("/")

    with StreamedClient(base_url=base) as client:
        print_banner("Streamed Sports", base, c)

        # --- Load sports once ---
        try:
            sports_raw = fetch_with_spinner("Fetching sports list", client.fetch_sports, c)
        except Exception as e:
            sys.stderr.write(f"{c.rose}✗ Failed to fetch sports: {e}{c.reset}\n")
            return 1

        sports = [StreamedSport.from_raw(raw) for raw in sports_raw]
        if not any(s.id.lower() == "popular" for s in sports):
            sports.insert(0, StreamedSport(id="popular", name="Popular"))

        sport_rows = [_streamed_sport_row(s, c) for s in sports]

        # ========== LEVEL 1: SPORT ==========
        while True:
            sport_idx = pick_from_list(
                f"Select a sport  {c.dim}({len(sports)} sports){c.reset}",
                sport_rows,
                c=c,
            )
            if sport_idx is None:
                print(f"\n{c.slate}  cancelled.{c.reset}")
                return 0

            chosen_sport = sports[sport_idx]
            print(f"\n  {c.bold}Selected sport:{c.reset} {c.sky}{chosen_sport.name}{c.reset}\n")

            try:
                if chosen_sport.id.lower() == "popular":
                    matches_raw = fetch_with_spinner("Fetching popular matches", client.fetch_popular_matches, c)
                else:
                    matches_raw = fetch_with_spinner(
                        f'Fetching matches for "{chosen_sport.name}"',
                        lambda: client.fetch_matches_by_sport(chosen_sport.id),
                        c,
                    )
            except Exception as e:
                sys.stderr.write(f"{c.rose}✗ Failed to fetch matches: {e}{c.reset}\n")
                continue

            matches = [StreamedMatch.from_raw(raw) for raw in matches_raw]
            if not matches:
                sys.stderr.write(f"{c.rose}✗ No matches found for {chosen_sport.name!r}{c.reset}\n")
                continue

            match_rows = [_streamed_match_row(m, c) for m in matches]

            # ========== LEVEL 2: MATCH ==========
            while True:
                match_idx = pick_from_list(
                    f"Select a match  {c.dim}({len(matches)} matches){c.reset}",
                    match_rows,
                    c=c,
                )
                if match_idx is None:
                    break  # back to sport list

                chosen_match = matches[match_idx]
                print(f"\n  {c.bold}Selected match:{c.reset} {c.sky}{chosen_match.display_title()}{c.reset}\n")

                try:
                    streams_raw = fetch_with_spinner(
                        f'Fetching streams for "{chosen_match.display_title()}"',
                        lambda: client.fetch_streams_for_match(chosen_match),
                        c,
                    )
                except Exception as e:
                    sys.stderr.write(f"{c.rose}✗ Failed to fetch streams: {e}{c.reset}\n")
                    continue

                streams = [StreamedStream.from_raw(raw) for raw in streams_raw]
                if not streams:
                    sys.stderr.write(f"{c.rose}✗ No streams available for this match{c.reset}\n")
                    continue

                stream_rows = [_streamed_stream_row(s, c) for s in streams]

                # ========== LEVEL 3: STREAM ==========
                while True:
                    stream_idx = pick_from_list(
                        f"Select a stream  {c.dim}({len(streams)} streams){c.reset}",
                        stream_rows,
                        c=c,
                    )
                    if stream_idx is None:
                        break  # back to match list

                    chosen_stream = streams[stream_idx]
                    print(f"\n  {c.bold}Selected stream:{c.reset} {c.sky}#{chosen_stream.stream_no} {chosen_stream.language}{c.reset}")

                    # --- Admin stream handling ---
                    if chosen_stream.is_admin:
                        print(f"\n  {c.warn}⚠ Admin streams cannot be extracted to m3u8 automatically.{c.reset}")
                        print(f"  {c.dim}They require a browser with JavaScript execution.{c.reset}")

                        if play_only:
                            print(chosen_stream.embed_url)
                            return 0

                        # ========== LEVEL 4: ACTION (admin) ==========
                        while True:
                            action = choose_playback_action(c, allow_mpv=False, back_label="Back to stream list")
                            if action in (None, "back"):
                                break  # back to stream list
                            if action == "browser":
                                open_in_browser(chosen_stream.embed_url, c)
                            elif action == "details":
                                _streamed_print_details(chosen_stream, None, c)
                                pause(c)
                        continue

                    # --- Non-admin: resolve m3u8 ---
                    try:
                        stream_url, stream_referer = fetch_with_spinner(
                            f'Resolving stream URL for "{chosen_stream.language}"',
                            lambda: client.fetch_stream_url(chosen_stream.embed_url),
                            c,
                        )
                    except Exception as e:
                        sys.stderr.write(f"{c.rose}✗ Failed to resolve stream: {e}{c.reset}\n")
                        continue

                    if play_only:
                        if stream_url and is_valid_url(stream_url):
                            print(stream_url)
                            return 0
                        sys.stderr.write(f"{c.rose}✗ Could not resolve a stream URL{c.reset}\n")
                        return 1

                    if not stream_url:
                        _streamed_print_details(chosen_stream, stream_url, c, referer=stream_referer)
                        pause(c)
                        continue

                    # ========== LEVEL 4: ACTION (regular) ==========
                    while True:
                        action = choose_playback_action(c, allow_mpv=True, back_label="Back to stream list")
                        if action in (None, "back"):
                            break  # back to stream list
                        if action == "mpv":
                            play_with_mpv(stream_url, c, referer=stream_referer)
                            break
                        if action == "browser":
                            open_in_browser(chosen_stream.embed_url, c)
                        elif action == "details":
                            _streamed_print_details(chosen_stream, stream_url, c, referer=stream_referer)
                            pause(c)

    return 0


# =========================================================================
# Entry point
# =========================================================================

SOURCE_KEYS = ("dlhd", "bintv", "ppv", "streamed")


def _source_rows(c: C) -> list[str]:
    return [
        f"{c.sage}●{c.reset}  {c.bold}DaddyLive{c.reset} — 24/7 TV channels  {c.dim}(dlhd.st){c.reset}",
        f"{c.warn}●{c.reset}  {c.bold}BINTV{c.reset} — live event streams  {c.dim}(bintv.cc){c.reset}",
        f"{c.amber}●{c.reset}  {c.bold}PPV{c.reset} — event index + substreams  {c.dim}(ppv.st){c.reset}",
        f"{c.sky}●{c.reset}  {c.bold}Streamed{c.reset} — sports matches  {c.dim}(streamed.pk / streamed.st){c.reset}",
    ]


def _dispatch(source: str, args: argparse.Namespace, use_color: bool) -> int:
    if source == "dlhd":
        selector = args.id if args.id is not None else args.channel
        return run_dlhd(use_color, play_only=args.play, channel_selector=selector)
    if source == "bintv":
        return run_bintv(
            use_color,
            category_filter=args.category,
            live_only=args.live_only,
            list_mode=args.list_mode,
            json_output=args.json,
        )
    if source == "ppv":
        return run_ppv(use_color, api_base=args.api, show_default=args.show_default)
    if source == "streamed":
        return run_streamed(use_color, play_only=args.play, base_url=args.base)
    sys.stderr.write(f"error: unknown source {source!r}\n")
    return 2


def _default_args(source: str) -> argparse.Namespace:
    """Arguments used when a source is launched from the interactive picker."""
    if source == "dlhd":
        return argparse.Namespace(play=False, channel=None, id=None)
    if source == "bintv":
        return argparse.Namespace(category=None, live_only=False, list_mode=False, json=False)
    if source == "ppv":
        return argparse.Namespace(
            api=os.environ.get("PPV_API_BASE", PPV_DEFAULT_API_BASE),
            show_default=False,
        )
    return argparse.Namespace(play=False, base=STREAMED_DEFAULT_BASE)


def build_parser() -> argparse.ArgumentParser:
    p = argparse.ArgumentParser(
        prog="streams.py",
        description=(
            "Browse live streams from DaddyLive, BINTV, PPV and Streamed in one "
            "terminal app. Run without a SOURCE to pick one interactively."
        ),
    )
    p.add_argument(
        "--raw",
        action="store_true",
        help="disable ANSI colours (accepted anywhere on the command line)",
    )
    subs = p.add_subparsers(dest="source", metavar="SOURCE")

    d = subs.add_parser("dlhd", help="DaddyLive 24/7 TV channels (dlhd.st)")
    d.add_argument("--play", action="store_true",
                   help="only print the decrypted m3u8 stream URL")
    sel = d.add_mutually_exclusive_group()
    sel.add_argument("--channel", metavar="NAME",
                     help="select a channel by name (substring match, must be unambiguous)")
    sel.add_argument("--id", metavar="ID",
                     help="select a channel by exact id")

    b = subs.add_parser("bintv", help="bintv.cc live event index")
    b.add_argument("--category", "-c", default=None, help="filter to a specific category")
    b.add_argument("--live-only", "-l", action="store_true", help="show only live events")
    b.add_argument("--list", action="store_true", dest="list_mode", help="plain-text list output")
    b.add_argument("--json", action="store_true", help="JSON output (for scripting)")

    v = subs.add_parser("ppv", help="ppv.st event index + substreams")
    v.add_argument("--api", default=os.environ.get("PPV_API_BASE", PPV_DEFAULT_API_BASE),
                   help=f"API base URL (default: {PPV_DEFAULT_API_BASE})")
    v.add_argument("--show-default", action="store_true",
                   help="also print the default embed before the source picker")

    s = subs.add_parser("streamed", help="Streamed.pk / Streamed.st sports streams")
    s.add_argument("--play", action="store_true",
                   help="only print the resolved m3u8 URL (or embed URL for admin streams)")
    s.add_argument("--base", metavar="URL", default=STREAMED_DEFAULT_BASE,
                   help=f"base URL (default: {STREAMED_DEFAULT_BASE}); "
                        f"can also be set via the STREAMED_BASE env var")

    return p


def main(argv: list[str] | None = None) -> int:
    argv = list(sys.argv[1:] if argv is None else argv)

    # `--raw` is accepted anywhere on the command line, so fish it out
    # before argparse sees it (subcommand flags come after the source name).
    use_raw = "--raw" in argv
    argv = [a for a in argv if a != "--raw"]

    args = build_parser().parse_args(argv)
    use_color = enable_colors(use_raw)

    if getattr(args, "source", None):
        return _dispatch(args.source, args, use_color)

    # No subcommand → interactive source picker (loops until Esc).
    c = C(use_color)
    print_banner("Stream Sources", "dlhd · bintv · ppv · streamed", c)

    while True:
        idx = pick_from_list(
            f"Select a source  {c.dim}(Esc to quit){c.reset}",
            _source_rows(c),
            c=c,
        )
        if idx is None:
            print(f"\n{c.slate}  bye.{c.reset}")
            return 0

        source = SOURCE_KEYS[idx]
        try:
            _dispatch(source, _default_args(source), use_color)
        except SystemExit as exc:
            # e.g. missing dependency for the chosen source — back to picker.
            if exc.code not in (None, 0):
                sys.stderr.write(f"{c.rose}✗ source exited with code {exc.code}{c.reset}\n")
        print()


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except KeyboardInterrupt:
        print()
        raise SystemExit(130)
