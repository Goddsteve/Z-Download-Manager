#!/usr/bin/env python3

import base64
import ipaddress
import json
import mimetypes
import os
import re
import shutil
import socket
import subprocess
import sys
import threading
import time
import uuid
from urllib.parse import parse_qs, unquote, urlparse

import requests
from PyQt6.QtCore import QObject, QPointF, QRectF, QSize, Qt, QTimer, QUrl, pyqtSignal
from PyQt6.QtGui import (
    QColor, QDesktopServices, QFont, QIcon, QPainter, QPainterPath, QPen, QPixmap, QPolygonF,
)
from PyQt6.QtWidgets import (
    QApplication, QButtonGroup, QCheckBox, QComboBox, QDialog, QFileDialog, QFrame, QHBoxLayout,
    QLabel, QLineEdit, QMainWindow, QMenu, QMessageBox, QProgressBar, QPushButton, QScrollArea,
    QSizePolicy, QSpinBox, QSystemTrayIcon, QToolButton, QVBoxLayout, QWidget,
)

try:
    import dns.resolver as _dns_resolver
except Exception:
    _dns_resolver = None


APP_NAME = "Z-Manager"
BRIDGE_HOST, BRIDGE_PORT = "127.0.0.1", 9420
STATE_FILE = os.path.join(os.path.expanduser("~"), "zmanager_state.json")
CONFIG_FILE = os.path.join(os.path.expanduser("~"), "zmanager_config.json")
USER_AGENT = "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 Z-Manager/2.0"

MIN_SEGMENT = 512 * 1024
MAX_SEGMENTS = 16
MAX_RETRIES = 5
RETRY_STATUS = {408, 425, 429, 500, 502, 503, 504}

DEFAULT_CONFIG = {
    "download_folder": os.path.join(os.path.expanduser("~"), "Downloads"),
    "connections": 8,
    "max_concurrent": 3,
    "speed_limit_kb": 0,
    "dns": "system",
    "fastest_server": True,
    "sort_by_type": False,
    "notifications": True,
    "sounds": True,
    "keep_in_tray": True,
}
DNS_SERVERS = {"system": None, "cloudflare": "1.1.1.1", "google": "8.8.8.8", "quad9": "9.9.9.9"}

CATEGORIES = {
    "Video": {"mp4", "mkv", "avi", "mov", "wmv", "webm", "flv", "m4v", "mpg", "mpeg", "ts"},
    "Music": {"mp3", "flac", "wav", "aac", "ogg", "m4a", "opus", "wma"},
    "Images": {"jpg", "jpeg", "png", "gif", "webp", "bmp", "svg", "tiff", "heic", "psd"},
    "Documents": {"pdf", "doc", "docx", "xls", "xlsx", "ppt", "pptx", "txt", "epub", "csv", "odt", "rtf"},
    "Archives": {"zip", "rar", "7z", "tar", "gz", "bz2", "xz", "iso", "tgz", "zst"},
    "Programs": {"exe", "msi", "dmg", "pkg", "deb", "rpm", "apk", "appimage", "bat", "sh"},
}


def format_size(n):
    n = float(n or 0)
    for unit in ("B", "KB", "MB", "GB", "TB"):
        if n < 1024 or unit == "TB":
            decimals = 0 if unit == "B" else (2 if unit in ("GB", "TB") else 1)
            return f"{n:.{decimals}f} {unit}"
        n /= 1024


def format_eta(seconds):
    seconds = int(max(seconds, 0))
    if seconds < 60:
        return f"{seconds}s"
    if seconds < 3600:
        return f"{seconds // 60}m {seconds % 60:02d}s"
    return f"{seconds // 3600}h {(seconds % 3600) // 60:02d}m"


def sanitize_filename(name):
    name = re.split(r"[\\/]", name or "")[-1]
    name = re.sub(r'[<>:"|?*\x00-\x1f]', "_", name).strip(" .")
    return name[:180]


def filename_from_headers(headers):
    cd = headers.get("Content-Disposition", "") or ""
    m = re.search(r"filename\*\s*=\s*([^']*)'[^']*'([^;]+)", cd, re.I)
    if m:
        try:
            return unquote(m.group(2).strip().strip('"'), encoding=(m.group(1) or "utf-8"))
        except (LookupError, ValueError):
            pass
    m = re.search(r'filename\s*=\s*"([^"]+)"', cd, re.I) or re.search(r"filename\s*=\s*([^;]+)", cd, re.I)
    if m:
        return unquote(m.group(1).strip().strip('"'))
    return ""


def category_of(filename):
    ext = os.path.splitext(filename)[1][1:].lower()
    for cat, exts in CATEGORIES.items():
        if ext in exts:
            return cat
    return "Other"


def part_path(path, i):
    return f"{path}.zpart{i}"


def has_parts(path):
    return any(os.path.exists(part_path(path, i)) for i in range(MAX_SEGMENTS))


def remove_parts(path):
    for i in range(MAX_SEGMENTS):
        try:
            os.remove(part_path(path, i))
        except OSError:
            pass
    try:
        os.remove(path + ".zmerge")
    except OSError:
        pass


def unique_path(path, is_taken=None):
    base, ext = os.path.splitext(path)
    if base.lower().endswith(".tar"):
        base, ext = base[:-4], ".tar" + ext
    cand, n = path, 1
    while os.path.exists(cand) or has_parts(cand) or (is_taken and is_taken(cand)):
        cand = f"{base} ({n}){ext}"
        n += 1
    return cand


def load_json(path, default):
    try:
        with open(path, "r", encoding="utf-8") as fh:
            return json.load(fh)
    except (OSError, ValueError):
        return default


def save_json(path, obj):
    tmp = path + ".tmp"
    try:
        with open(tmp, "w", encoding="utf-8") as fh:
            json.dump(obj, fh, indent=2)
        os.replace(tmp, path)
    except OSError:
        pass


_dns_server = None
_dns_cache = {}
_orig_getaddrinfo = socket.getaddrinfo


def set_dns_server(ip):
    global _dns_server
    _dns_server = ip
    _dns_cache.clear()


def _lookup(host):
    hit = _dns_cache.get(host)
    if hit and hit[1] > time.time():
        return hit[0]
    if not _dns_resolver or not _dns_server:
        return None
    try:
        res = _dns_resolver.Resolver(configure=False)
        res.nameservers = [_dns_server]
        res.lifetime = 4
        answer = res.resolve(host, "A")
        ips = [r.to_text() for r in answer]
        _dns_cache[host] = (ips, time.time() + max(30, min(answer.rrset.ttl, 600)))
        return ips
    except Exception:
        return None


_fastest_on = True
_rank_cache = {}
_rank_lock = threading.Lock()
_rank_turn = 0
RANK_TTL = 120
RANK_TIMEOUT = 2.5
RANK_MAX_IPS = 8


def set_fastest_server(on):
    global _fastest_on
    _fastest_on = bool(on)
    with _rank_lock:
        _rank_cache.clear()


def _tcp_time(info, results, i):
    family, socktype, proto, _canon, addr = info
    t0 = time.perf_counter()
    s = None
    try:
        s = socket.socket(family, socktype, proto)
        s.settimeout(RANK_TIMEOUT)
        s.connect(addr)
        results[i] = time.perf_counter() - t0
    except OSError:
        results[i] = float("inf")
    finally:
        if s is not None:
            try:
                s.close()
            except OSError:
                pass


def _rank(host, port, infos):
    global _rank_turn
    infos = [i for i in infos if i[1] == socket.SOCK_STREAM][:RANK_MAX_IPS] or infos
    if len(infos) < 2:
        return infos
    key = (host, port)
    now = time.time()
    with _rank_lock:
        hit = _rank_cache.get(key)
    if hit and hit[1] > now:
        ordered = hit[0]
    else:
        results = [float("inf")] * len(infos)
        threads = [threading.Thread(target=_tcp_time, args=(inf, results, i), daemon=True)
                   for i, inf in enumerate(infos)]
        for t in threads:
            t.start()
        for t in threads:
            t.join(RANK_TIMEOUT + 0.5)
        order = sorted(range(len(infos)), key=lambda i: results[i])
        ordered = [(infos[i], results[i]) for i in order]
        with _rank_lock:
            _rank_cache[key] = (ordered, now + RANK_TTL)
    best = ordered[0][1]
    good = [inf for inf, t in ordered if t <= best * 1.5 + 0.015]
    rest = [inf for inf, t in ordered if inf not in good]
    with _rank_lock:
        _rank_turn += 1
        turn = _rank_turn
    k = turn % len(good)
    return good[k:] + good[:k] + rest


def _getaddrinfo(host, port, *args, **kwargs):
    is_name = isinstance(host, str) and host != "localhost"
    if is_name:
        try:
            ipaddress.ip_address(host)
            is_name = False
        except ValueError:
            pass
    if not is_name:
        return _orig_getaddrinfo(host, port, *args, **kwargs)

    infos = None
    if _dns_server:
        ips = _lookup(host)
        if ips:
            infos = []
            for ip in ips:
                try:
                    infos += _orig_getaddrinfo(ip, port, *args, **kwargs)
                except OSError:
                    pass
    if not infos:
        infos = _orig_getaddrinfo(host, port, *args, **kwargs)
    if _fastest_on and port in (80, 443, 8080, 8443) and len(infos) > 1:
        try:
            infos = _rank(host, port, infos)
        except Exception:
            pass
    return infos


socket.getaddrinfo = _getaddrinfo


class RateLimiter:
    def __init__(self):
        self.rate = 0
        self._next = 0.0
        self._lock = threading.Lock()

    def set_rate(self, bytes_per_sec):
        with self._lock:
            self.rate = max(int(bytes_per_sec), 0)

    def consume(self, n, halt=None):
        if self.rate <= 0:
            return
        with self._lock:
            now = time.monotonic()
            start = max(now, self._next)
            self._next = start + n / self.rate
            wait = start - now
        if wait > 0:
            if halt is not None:
                halt.wait(wait)
            else:
                time.sleep(wait)


class FatalError(Exception):
    pass


def describe_error(exc):
    if isinstance(exc, FatalError):
        return str(exc)
    if isinstance(exc, requests.exceptions.SSLError):
        return "Secure connection failed (SSL)"
    if isinstance(exc, requests.exceptions.Timeout):
        return "Connection timed out"
    if isinstance(exc, requests.exceptions.ConnectionError):
        return "Couldn't connect to the server"
    if isinstance(exc, PermissionError):
        return "Permission denied writing the file"
    if isinstance(exc, OSError) and getattr(exc, "errno", None) == 28:
        return "Disk is full"
    return (str(exc) or exc.__class__.__name__)[:140]


def http_message(code):
    known = {401: "Login required", 403: "Access denied", 404: "File not found",
             410: "Link expired", 429: "Too many requests"}
    return f"{known.get(code, 'Server error')} (HTTP {code})"


def _noop(*args):
    pass


class Downloader(threading.Thread):
    def __init__(self, url, save_path, *, referrer="", total_hint=0, segments_hint=0,
                 connections=8, limiter=None, is_taken=None, cookies=None, user_agent="",
                 on_progress=None, on_state=None, on_rename=None, on_info=None):
        super().__init__(daemon=True, name="zm-download")
        self.url = url
        self.save_path = save_path
        self.referrer = referrer
        self.cookies = cookies or []
        self.user_agent = user_agent or ""
        self.total_hint = total_hint
        self.segments_hint = segments_hint
        self.connections = max(1, min(int(connections), MAX_SEGMENTS))
        self.limiter = limiter or RateLimiter()
        self.is_taken = is_taken
        self.on_progress = on_progress or _noop
        self.on_state = on_state or _noop
        self.on_rename = on_rename or _noop
        self.on_info = on_info or _noop
        self._halt = threading.Event()
        self._mode = None
        self._errors = []
        self._lock = threading.Lock()

    def pause(self):
        self._mode = "pause"
        self._halt.set()

    def cancel(self):
        self._mode = "cancel"
        self._halt.set()

    def _interrupted(self):
        if self._mode == "pause":
            self.on_state("PAUSED", "")
            return True
        if self._mode == "cancel":
            remove_parts(self.save_path)
            self.on_state("CANCELLED", "")
            return True
        return False

    def run(self):
        try:
            self._download()
        except Exception as exc:
            if not self._interrupted():
                self.on_state("FAILED", describe_error(exc))

    def _make_session(self):
        session = requests.Session()
        for c in self.cookies:
            try:
                session.cookies.set(c["name"], c["value"], domain=c.get("domain") or None,
                                    path=c.get("path") or "/", secure=bool(c.get("secure")))
            except Exception:
                pass
        return session

    def _probe(self, headers):
        h = dict(headers, Range="bytes=0-0")
        last = None
        session = self._make_session()
        for attempt in range(3):
            if self._halt.is_set():
                return 0, False, "", ""
            try:
                with session.get(self.url, headers=h, stream=True, timeout=(15, 30)) as resp:
                    code = resp.status_code
                    ctype = resp.headers.get("Content-Type", "").split(";")[0].strip().lower()
                    suggested = filename_from_headers(resp.headers)
                    if code == 206:
                        tail = resp.headers.get("Content-Range", "").rsplit("/", 1)[-1].strip()
                        total = int(tail) if tail.isdigit() else 0
                        return total, total > 0, suggested, ctype
                    if code == 416:
                        return 0, False, suggested, ctype
                    if code == 200:
                        cl = resp.headers.get("Content-Length", "")
                        return (int(cl) if cl.isdigit() else 0), False, suggested, ctype
                    if code in RETRY_STATUS:
                        last = FatalError(http_message(code))
                    else:
                        raise FatalError(http_message(code))
            except requests.RequestException as exc:
                last = exc
            self._halt.wait(1.5 * (attempt + 1))
        raise last or FatalError("Couldn't reach the server")

    def _adopt_name(self, suggested, ctype):
        path = self.save_path
        if os.path.exists(path) or has_parts(path):
            return path
        name = sanitize_filename(suggested)
        if not name:
            base = os.path.basename(path)
            if not os.path.splitext(base)[1] and ctype:
                ext = mimetypes.guess_extension(ctype)
                if ext and ext != ".bin":
                    name = base + ext
        if name and name != os.path.basename(path):
            path = unique_path(os.path.join(os.path.dirname(path), name), self.is_taken)
            self.save_path = path
            self.on_rename(path)
        return path

    def _download(self):
        headers = {"User-Agent": self.user_agent or USER_AGENT, "Accept": "*/*", "Accept-Encoding": "identity"}
        if self.referrer:
            headers["Referer"] = self.referrer

        self.on_state("DOWNLOADING", "Connecting…")
        total, ranges, suggested, ctype = self._probe(headers)
        if self._interrupted():
            return

        save_path = self._adopt_name(suggested, ctype)
        directory = os.path.dirname(save_path) or "."
        os.makedirs(directory, exist_ok=True)

        existing = [i for i in range(MAX_SEGMENTS) if os.path.exists(part_path(save_path, i))]
        resumable = bool(existing) and ranges and self.segments_hint >= 1 and self.total_hint in (0, total)
        if existing and not resumable:
            remove_parts(save_path)
        if resumable:
            n = min(self.segments_hint, MAX_SEGMENTS)
        elif ranges and self.connections > 1 and total >= 2 * MIN_SEGMENT:
            n = max(1, min(self.connections, total // MIN_SEGMENT))
        else:
            n = 1

        if ranges and n > 1:
            size = total // n
            bounds = [(i * size, total - 1 if i == n - 1 else (i + 1) * size - 1) for i in range(n)]
        else:
            n = 1
            bounds = [(0, total - 1 if total else None)]
        for i in range(n, MAX_SEGMENTS):
            try:
                os.remove(part_path(save_path, i))
            except OSError:
                pass
        self.on_info(total, n)

        counters = []
        for i, (s, e) in enumerate(bounds):
            p = part_path(save_path, i)
            sz = os.path.getsize(p) if os.path.exists(p) else 0
            if e is not None and sz > e - s + 1:
                open(p, "wb").close()
                sz = 0
            counters.append(sz)

        if total:
            free = shutil.disk_usage(directory).free
            if total - sum(counters) > free - 1024 * 1024:
                raise FatalError("Not enough disk space")

        self.on_state("DOWNLOADING", "")
        threads = []
        for i, (s, e) in enumerate(bounds):
            if e is not None and counters[i] >= e - s + 1:
                continue
            th = threading.Thread(target=self._segment_main, daemon=True,
                                  args=(i, s, e, ranges, headers, counters, part_path(save_path, i)))
            th.start()
            threads.append(th)

        last_t, last_b, speed = time.monotonic(), sum(counters), 0.0
        self.on_progress(last_b, total, 0.0)
        while any(t.is_alive() for t in threads):
            time.sleep(0.3)
            now, done = time.monotonic(), sum(counters)
            dt = now - last_t
            if dt > 0:
                inst = (done - last_b) / dt
                speed = inst if speed == 0 else speed * 0.6 + inst * 0.4
                last_t, last_b = now, done
            self.on_progress(done, total, speed)
        for t in threads:
            t.join()
        self.on_progress(sum(counters), total, 0.0)

        if self._interrupted():
            return
        if self._errors:
            raise self._errors[0]

        self.on_state("FINALIZING", "")
        for i, (s, e) in enumerate(bounds):
            p = part_path(save_path, i)
            got = os.path.getsize(p) if os.path.exists(p) else 0
            if e is not None and got != e - s + 1:
                raise FatalError("Download incomplete, try resuming")
        if n == 1:
            os.replace(part_path(save_path, 0), save_path)
        else:
            tmp = save_path + ".zmerge"
            with open(tmp, "wb") as out:
                for i in range(n):
                    p = part_path(save_path, i)
                    with open(p, "rb") as src:
                        shutil.copyfileobj(src, out, 1024 * 1024)
                    os.remove(p)
            os.replace(tmp, save_path)
        final = os.path.getsize(save_path)
        self.on_progress(final, total or final, 0.0)
        self.on_state("COMPLETED", "")

    def _segment_main(self, idx, start, end, ranged, headers, counters, path):
        try:
            self._segment(idx, start, end, ranged, headers, counters, path)
        except Exception as exc:
            with self._lock:
                self._errors.append(exc)
            self._halt.set()

    def _segment(self, idx, start, end, ranged, headers, counters, path):
        session = self._make_session()
        attempts = 0
        try:
            while not self._halt.is_set():
                done = os.path.getsize(path) if (ranged and os.path.exists(path)) else 0
                seg_len = (end - start + 1) if end is not None else None
                if seg_len is not None and done >= seg_len:
                    counters[idx] = seg_len
                    return
                counters[idx] = done
                h = dict(headers)
                if ranged:
                    h["Range"] = f"bytes={start + done}-{end}"
                got_data = False
                try:
                    with session.get(self.url, headers=h, stream=True, timeout=(15, 30)) as resp:
                        code = resp.status_code
                        if (ranged and code != 206) or (not ranged and code >= 400):
                            if code in RETRY_STATUS:
                                raise ConnectionError(http_message(code))
                            raise FatalError(http_message(code) if code >= 400
                                             else "Server stopped supporting resume")
                        with open(path, "ab" if done else "wb") as fh:
                            for chunk in resp.iter_content(64 * 1024):
                                if self._halt.is_set():
                                    return
                                if not chunk:
                                    continue
                                self.limiter.consume(len(chunk), self._halt)
                                fh.write(chunk)
                                counters[idx] += len(chunk)
                                got_data = True
                                if seg_len is not None and counters[idx] >= seg_len:
                                    break
                    if seg_len is None or counters[idx] >= seg_len:
                        return
                    raise ConnectionError("Connection closed early")
                except FatalError:
                    raise
                except Exception:
                    if self._halt.is_set():
                        return
                    attempts = 0 if got_data else attempts + 1
                    if not ranged or attempts > MAX_RETRIES:
                        raise
                    self._halt.wait(min(2 ** attempts, 10))
        finally:
            session.close()


class BridgeServer(threading.Thread):
    def __init__(self, on_request, on_status, host=BRIDGE_HOST, port=BRIDGE_PORT, on_handoff=None):
        super().__init__(daemon=True, name="zm-bridge")
        self.on_request = on_request
        self.on_status = on_status
        self.on_handoff = on_handoff or (lambda task_id: None)
        self.statuses = {}
        self.host, self.port = host, port
        self._quit = threading.Event()

    def shutdown(self):
        self._quit.set()

    def run(self):
        srv = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
        try:
            srv.bind((self.host, self.port))
            srv.listen(16)
        except OSError:
            self.on_status(False, f"Port {self.port} is busy. Is Z-Manager already running?")
            return
        srv.settimeout(0.5)
        self.on_status(True, "Browser bridge ready")
        while not self._quit.is_set():
            try:
                client, _ = srv.accept()
            except socket.timeout:
                continue
            except OSError:
                break
            threading.Thread(target=self._handle, args=(client,), daemon=True).start()
        srv.close()

    @staticmethod
    def _reply(client, code, body="", extra=None):
        reasons = {200: "OK", 204: "No Content", 400: "Bad Request", 403: "Forbidden", 405: "Method Not Allowed"}
        data = body.encode()
        head = [f"HTTP/1.1 {code} {reasons.get(code, 'OK')}", "Content-Type: application/json",
                f"Content-Length: {len(data)}", "Connection: close"]
        head += [f"{k}: {v}" for k, v in (extra or {}).items()]
        client.sendall(("\r\n".join(head) + "\r\n\r\n").encode() + data)

    @staticmethod
    def parse_payload(text):
        text = text.strip()
        try:
            obj = json.loads(text)
        except ValueError:
            obj = {"url": text}
        if not isinstance(obj, dict):
            return None
        url = str(obj.get("url", "")).strip()
        if not re.match(r"^https?://", url, re.I):
            return None
        cookies = []
        for c in (obj.get("cookies") or [])[:300]:
            if isinstance(c, dict) and c.get("name") is not None and c.get("value") is not None:
                cookies.append({"name": str(c["name"]), "value": str(c["value"]),
                                "domain": str(c.get("domain", "") or ""), "path": str(c.get("path", "/") or "/"),
                                "secure": bool(c.get("secure", False))})
        return {"url": url, "referrer": str(obj.get("referrer", "") or ""),
                "filename": str(obj.get("filename", "") or ""),
                "cookies": cookies, "userAgent": str(obj.get("userAgent", "") or "")[:500]}

    def _handle(self, client):
        try:
            client.settimeout(5)
            data = b""
            while b"\r\n\r\n" not in data and len(data) < 65536:
                chunk = client.recv(4096)
                if not chunk:
                    break
                data += chunk
            head, _, body = data.partition(b"\r\n\r\n")
            lines = head.decode("latin-1").split("\r\n")
            parts = lines[0].split(" ") if lines and lines[0] else []
            method = parts[0].upper() if parts else ""
            path = parts[1] if len(parts) > 1 else "/"
            headers = {}
            for ln in lines[1:]:
                if ":" in ln:
                    k, v = ln.split(":", 1)
                    headers[k.strip().lower()] = v.strip()

            origin = headers.get("origin", "")
            from_ext = origin.startswith(("chrome-extension://", "moz-extension://", "edge-extension://"))
            cors = ({"Access-Control-Allow-Origin": origin, "Vary": "Origin",
                     "Access-Control-Allow-Headers": "Content-Type, X-ZManager",
                     "Access-Control-Allow-Methods": "POST, GET, OPTIONS"} if from_ext else {})

            if method == "OPTIONS":
                return self._reply(client, 204, "", cors)
            if method == "GET":
                if path.startswith("/status"):
                    if origin and not from_ext:
                        return self._reply(client, 403, '{"error":"forbidden"}')
                    ids = parse_qs(urlparse(path).query).get("ids", [""])[0].split(",")
                    known = {i: self.statuses[i] for i in ids if i in self.statuses}
                    return self._reply(client, 200, json.dumps(known), cors)
                return self._reply(client, 200, '{"app":"z-manager"}', cors)
            if method != "POST":
                return self._reply(client, 405, "", cors)
            if (origin and not from_ext) or headers.get("x-zmanager") != "1":
                return self._reply(client, 403, '{"error":"forbidden"}')

            length = min(int(headers.get("content-length") or 0), 1048576)
            while len(body) < length:
                chunk = client.recv(4096)
                if not chunk:
                    break
                body += chunk
            if path.startswith("/handoff"):
                try:
                    task_id = str(json.loads(body.decode("utf-8", "replace")).get("id", ""))
                except ValueError:
                    task_id = ""
                if task_id:
                    self.on_handoff(task_id)
                return self._reply(client, 200, '{"ok":true}', cors)
            payload = self.parse_payload(body.decode("utf-8", "replace"))
            if not payload:
                return self._reply(client, 400, '{"error":"bad url"}', cors)
            payload["id"] = uuid.uuid4().hex[:12]
            self.statuses[payload["id"]] = "QUEUED"
            self.on_request(payload)
            self._reply(client, 200, json.dumps({"ok": True, "id": payload["id"]}), cors)
        except Exception:
            pass
        finally:
            try:
                client.close()
            except OSError:
                pass



C = {
    "bg": "#0A0A0A", "surface": "#121212", "surface2": "#1A1A1A",
    "border": "#222222", "border2": "#303030",
    "text": "#F1F1EE", "muted": "#8C8C86", "faint": "#55554F",
    "accent": "#BDBDB8", "accent_hover": "#DADAD5",
    "ok": "#BDBDB8", "warn": "#F0A94B", "bad": "#FF5D5D",
}
ACTIVE_STATES = ("DOWNLOADING", "FINALIZING")
VALID_STATES = ("QUEUED", "DOWNLOADING", "FINALIZING", "PAUSED", "COMPLETED", "FAILED", "CANCELLED")

QSS = """
* { font-family: "Segoe UI Variable Text", "Segoe UI", "Inter", "SF Pro Text", "Helvetica Neue", Arial, sans-serif;
    font-size: 13px; color: @text; }
QMainWindow, QDialog, QWidget#central { background: @bg; }
QLabel { background: transparent; }
QLabel#title { font-size: 17px; font-weight: 600; }
QLabel#emptyTitle { font-size: 15px; font-weight: 600; }
QLabel#muted { color: @muted; }
QLabel#footer { color: @faint; font-size: 12px; }
QLabel#section { color: @faint; font-size: 11px; font-weight: 600; }
QLabel#hint { color: @faint; font-size: 12px; }
QLabel#dot { background: @faint; border-radius: 3px; min-width: 6px; max-width: 6px; min-height: 6px; max-height: 6px; }
QLabel#dot[ok="true"] { background: @ok; }
QLabel#dot[ok="false"] { background: @bad; }
QFrame#hairline { background: @border; border: none; }

QLineEdit { background: @surface; border: 1px solid @border; border-radius: 10px; padding: 10px 14px;
            selection-background-color: @accent; selection-color: @bg; }
QLineEdit:focus { border-color: @accent; }
QLineEdit#search { padding: 6px 12px 6px 4px; font-size: 12px; border-radius: 9px; }
QLineEdit#flat { background: transparent; border: none; border-bottom: 1px solid transparent; border-radius: 0;
                 padding: 4px 0; color: @muted; }
QLineEdit#flat:focus { color: @text; border-bottom: 1px solid @accent; }

QPushButton { background: transparent; border: 1px solid @border2; border-radius: 9px; padding: 8px 16px; }
QPushButton:hover { background: @surface2; }
QPushButton#primary { background: @accent; border: none; color: @bg; font-weight: 600; padding: 9px 22px; }
QPushButton#primary:hover { background: @accent_hover; }
QPushButton#ghost { border: none; color: @muted; padding: 9px 14px; }
QPushButton#ghost:hover { color: @text; background: transparent; }
QPushButton#pill { background: transparent; border: none; border-radius: 14px; padding: 5px 13px; color: @faint; }
QPushButton#pill:hover { color: @text; }
QPushButton#pill:checked { background: @surface2; color: @text; }

QToolButton { background: transparent; border: none; border-radius: 8px; padding: 6px; }
QToolButton:hover { background: @surface2; }
QToolButton:disabled { background: transparent; }

QFrame#card { background: @surface; border: 1px solid @border; border-radius: 12px; }
QFrame#card:hover { border-color: @border2; }
QLabel#badge { background: @surface2; color: @muted; border-radius: 8px; font-size: 10px; font-weight: 600; }
QLabel#name { font-size: 13px; font-weight: 600; }
QLabel#meta { color: @muted; font-size: 12px; }
QLabel#meta[kind="bad"] { color: @bad; }
QLabel#pct { color: @muted; font-size: 12px; font-weight: 600; }
QLabel#pct[kind="ok"] { color: @accent; }
QLabel#pct[kind="bad"] { color: @bad; }
QLabel#pct[kind="warn"] { color: @warn; }

QProgressBar { background: @surface2; border: none; border-radius: 1px; min-height: 3px; max-height: 3px;
               color: transparent; text-align: center; }
QProgressBar::chunk { background: @accent; border-radius: 1px; }
QProgressBar[state="done"]::chunk { background: @faint; }
QProgressBar[state="bad"]::chunk { background: @bad; }
QProgressBar[state="paused"]::chunk { background: @warn; }
QProgressBar[state="idle"]::chunk { background: @border2; }

QScrollArea, QWidget#taskList { background: transparent; border: none; }
QScrollBar:vertical { background: transparent; width: 8px; margin: 2px; }
QScrollBar::handle:vertical { background: @border2; border-radius: 3px; min-height: 30px; }
QScrollBar::handle:vertical:hover { background: @faint; }
QScrollBar::add-line:vertical, QScrollBar::sub-line:vertical { height: 0; }
QScrollBar::add-page:vertical, QScrollBar::sub-page:vertical { background: none; }

QSpinBox, QComboBox { background: @surface; border: 1px solid @border; border-radius: 8px; padding: 6px 10px;
                      min-width: 120px; selection-background-color: @accent; selection-color: @bg; }
QSpinBox:focus, QComboBox:focus { border-color: @accent; }
QSpinBox:disabled, QComboBox:disabled { color: @faint; }
QSpinBox::up-button, QSpinBox::down-button { width: 0; border: none; }
QComboBox::drop-down { border: none; width: 22px; }
QComboBox QAbstractItemView { background: @surface; border: 1px solid @border2; outline: 0;
                              selection-background-color: @surface2; selection-color: @text; }

QMenu { background: @surface; border: 1px solid @border2; padding: 6px; }
QMenu::item { padding: 7px 22px; border-radius: 6px; }
QMenu::item:selected { background: @surface2; }
QMenu::separator { height: 1px; background: @border; margin: 5px 8px; }
QToolTip { background: @surface2; color: @text; border: 1px solid @border2; padding: 5px 8px; }
QMessageBox { background: @bg; }
"""


def build_qss():
    out = QSS
    for key in sorted(C, key=len, reverse=True):
        out = out.replace("@" + key, C[key])
    return out


def repolish(widget):
    widget.style().unpolish(widget)
    widget.style().polish(widget)


_ICONS = {}


def icon(kind):
    if kind not in _ICONS:
        _ICONS[kind] = _draw_icon(kind)
    return _ICONS[kind]


def _draw_icon(kind, color="#8C8C86", size=18):
    scale = 2
    pm = QPixmap(size * scale, size * scale)
    pm.setDevicePixelRatio(scale)
    pm.fill(Qt.GlobalColor.transparent)
    p = QPainter(pm)
    p.setRenderHint(QPainter.RenderHint.Antialiasing)
    c = QColor(color)
    pen = QPen(c, 1.6)
    pen.setCapStyle(Qt.PenCapStyle.RoundCap)
    pen.setJoinStyle(Qt.PenJoinStyle.RoundJoin)
    p.setPen(pen)
    p.setBrush(Qt.BrushStyle.NoBrush)
    P = QPointF

    if kind == "play":
        p.setBrush(c)
        p.drawPolygon(QPolygonF([P(6.5, 4.5), P(14, 9), P(6.5, 13.5)]))
    elif kind == "pause":
        p.setPen(Qt.PenStyle.NoPen)
        p.setBrush(c)
        p.drawRoundedRect(QRectF(5, 4.5, 3.2, 9), 1, 1)
        p.drawRoundedRect(QRectF(9.8, 4.5, 3.2, 9), 1, 1)
    elif kind == "close":
        p.drawLine(P(5, 5), P(13, 13))
        p.drawLine(P(13, 5), P(5, 13))
    elif kind == "folder":
        path = QPainterPath()
        path.moveTo(3, 13.5)
        path.lineTo(3, 5)
        path.lineTo(7.5, 5)
        path.lineTo(9, 6.8)
        path.lineTo(15, 6.8)
        path.lineTo(15, 13.5)
        path.closeSubpath()
        p.drawPath(path)
    elif kind == "retry":
        p.drawArc(QRectF(3.5, 3.5, 11, 11), 45 * 16, 270 * 16)
        p.setBrush(c)
        p.drawPolygon(QPolygonF([P(14.6, 11.0), P(10.4, 12.2), P(13.6, 15.2)]))
    elif kind == "search":
        p.drawEllipse(QRectF(3.5, 3.5, 8, 8))
        p.drawLine(P(10, 10), P(14.5, 14.5))
    elif kind == "done":
        p.drawEllipse(QRectF(3, 3, 12, 12))
        path = QPainterPath()
        path.moveTo(6.2, 9.2)
        path.lineTo(8.2, 11.2)
        path.lineTo(11.8, 6.9)
        p.drawPath(path)
    elif kind == "settings":
        p.drawLine(P(3, 6), P(15, 6))
        p.drawLine(P(3, 12), P(15, 12))
        p.setBrush(QColor(C["bg"]))
        p.drawEllipse(P(6.5, 6), 2.1, 2.1)
        p.drawEllipse(P(11.5, 12), 2.1, 2.1)
    p.end()
    return QIcon(pm)


_LOGO_B64 = (
    "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"
)
_LOGO_GLYPH = None


def make_logo(size=64, tile=True):
    global _LOGO_GLYPH
    if _LOGO_GLYPH is None:
        _LOGO_GLYPH = QPixmap()
        _LOGO_GLYPH.loadFromData(base64.b64decode(_LOGO_B64))
    pm = QPixmap(size, size)
    pm.fill(Qt.GlobalColor.transparent)
    p = QPainter(pm)
    p.setRenderHint(QPainter.RenderHint.Antialiasing)
    p.setRenderHint(QPainter.RenderHint.SmoothPixmapTransform)
    if tile:
        p.setBrush(QColor("#141414"))
        p.setPen(Qt.PenStyle.NoPen)
        p.drawRoundedRect(QRectF(0, 0, size, size), size * 0.24, size * 0.24)
        pad = size * 0.2
    else:
        pad = 0
    p.drawPixmap(QRectF(pad, pad, size - 2 * pad, size - 2 * pad), _LOGO_GLYPH, QRectF(_LOGO_GLYPH.rect()))
    p.end()
    return pm


class ElidedLabel(QLabel):
    def __init__(self, text="", mode=Qt.TextElideMode.ElideMiddle, parent=None):
        super().__init__("", parent)
        self._full = text
        self._mode = mode
        self.setSizePolicy(QSizePolicy.Policy.Ignored, QSizePolicy.Policy.Preferred)
        self.setMinimumWidth(20)

    def setFullText(self, text):
        if text != self._full:
            self._full = text
            self.setToolTip(text)
        self._update()

    def resizeEvent(self, event):
        super().resizeEvent(event)
        self._update()

    def _update(self):
        super().setText(self.fontMetrics().elidedText(self._full, self._mode, max(self.width() - 2, 0)))


class DownloadTask(QObject):
    changed = pyqtSignal()
    status_changed = pyqtSignal(object)
    _progress = pyqtSignal(object, object, float)
    _state = pyqtSignal(str, str)
    _renamed = pyqtSignal(str)
    _info = pyqtSignal(object, int)

    def __init__(self, data):
        super().__init__()
        self.id = data["id"]
        self.url = data["url"]
        self.save_path = data["save_path"]
        self.status = data.get("status", "QUEUED")
        self.referrer = data.get("referrer", "")
        self.cookies = data.get("cookies") or []
        self.user_agent = data.get("user_agent", "")
        self.total = max(int(data.get("total", 0) or 0), 0)
        self.downloaded = max(int(data.get("downloaded", 0) or 0), 0)
        self.segments = int(data.get("segments", 0) or 0)
        self.added = data.get("added", time.time())
        self.finished_at = data.get("finished_at", 0)
        self.error = data.get("error", "")
        self.message = ""
        self.speed = 0.0
        self.worker = None
        self._progress.connect(self._on_progress)
        self._state.connect(self._on_state)
        self._renamed.connect(self._on_renamed)
        self._info.connect(self._on_info)

    def to_dict(self):
        return {"id": self.id, "url": self.url, "save_path": self.save_path, "status": self.status,
                "referrer": self.referrer, "total": self.total, "downloaded": self.downloaded,
                "segments": self.segments, "added": self.added, "finished_at": self.finished_at,
                "error": self.error}

    @property
    def filename(self):
        return os.path.basename(self.save_path)

    @property
    def active(self):
        return self.status in ACTIVE_STATES

    @property
    def fraction(self):
        return min(self.downloaded / self.total, 1.0) if self.total > 0 else 0.0

    @property
    def worker_alive(self):
        return bool(self.worker and self.worker.is_alive())

    def start(self, cfg, limiter, is_taken):
        if self.worker_alive:
            self.worker.join(1.0)
            if self.worker_alive:
                return
        self.status, self.message, self.error, self.speed = "DOWNLOADING", "Connecting…", "", 0.0
        self.worker = Downloader(
            self.url, self.save_path, referrer=self.referrer, total_hint=self.total,
            segments_hint=self.segments, connections=cfg["connections"], limiter=limiter,
            is_taken=is_taken, cookies=self.cookies, user_agent=self.user_agent,
            on_progress=self._progress.emit, on_state=self._state.emit,
            on_rename=self._renamed.emit, on_info=self._info.emit)
        self.worker.start()
        self.changed.emit()
        self.status_changed.emit(self)

    def pause(self):
        if self.worker_alive:
            self.worker.pause()
            self.message = "Pausing…"
        elif self.status == "QUEUED":
            self.status = "PAUSED"
            self.status_changed.emit(self)
        self.changed.emit()

    def cancel(self):
        if self.worker_alive:
            self.worker.cancel()
            self.message = "Cancelling…"
        else:
            remove_parts(self.save_path)
            self.status, self.downloaded, self.speed = "CANCELLED", 0, 0.0
            self.status_changed.emit(self)
        self.changed.emit()

    def queue(self):
        if self.status in ("PAUSED", "FAILED", "CANCELLED"):
            self.status, self.error, self.message = "QUEUED", "", ""
            self.changed.emit()
            self.status_changed.emit(self)

    def _on_progress(self, done, total, speed):
        self.downloaded = done
        if total and total > 0:
            self.total = total
        self.speed = speed
        if self.message == "Connecting…":
            self.message = ""
        self.changed.emit()

    def _on_state(self, status, message):
        if status == "DOWNLOADING" and self.status != "DOWNLOADING":
            return
        self.status, self.message, self.speed = status, message, 0.0
        if status == "FAILED":
            self.error = message
        elif status == "COMPLETED":
            self.finished_at = time.time()
            self.downloaded = self.total or self.downloaded
        elif status == "CANCELLED":
            self.downloaded = 0
        self.changed.emit()
        self.status_changed.emit(self)

    def _on_renamed(self, path):
        self.save_path = path
        self.changed.emit()

    def _on_info(self, total, segments):
        self.segments = segments
        if total:
            self.total = total


class TaskCard(QFrame):
    requested = pyqtSignal(str, object)

    def __init__(self, task):
        super().__init__()
        self.task = task
        self.setObjectName("card")
        self._main_action = self._side_action = ""

        row = QHBoxLayout(self)
        row.setContentsMargins(16, 13, 10, 13)
        row.setSpacing(14)

        self.badge = QLabel()
        self.badge.setObjectName("badge")
        self.badge.setFixedSize(38, 38)
        self.badge.setAlignment(Qt.AlignmentFlag.AlignCenter)
        row.addWidget(self.badge)

        body = QVBoxLayout()
        body.setSpacing(7)
        top = QHBoxLayout()
        top.setSpacing(10)
        self.name = ElidedLabel()
        self.name.setObjectName("name")
        self.pct = QLabel()
        self.pct.setObjectName("pct")
        top.addWidget(self.name, 1)
        top.addWidget(self.pct)
        body.addLayout(top)
        self.bar = QProgressBar()
        self.bar.setRange(0, 1000)
        self.bar.setTextVisible(False)
        body.addWidget(self.bar)
        self.meta = ElidedLabel(mode=Qt.TextElideMode.ElideRight)
        self.meta.setObjectName("meta")
        body.addWidget(self.meta)
        row.addLayout(body, 1)

        btns = QHBoxLayout()
        btns.setSpacing(2)
        self.btn_main = self._tool_button(self._on_main)
        self.btn_side = self._tool_button(self._on_side)
        btns.addWidget(self.btn_main)
        btns.addWidget(self.btn_side)
        row.addLayout(btns)

        task.changed.connect(self.refresh)
        self.refresh()

    def _tool_button(self, slot):
        b = QToolButton()
        b.setFixedSize(34, 34)
        b.setIconSize(QSize(18, 18))
        b.setCursor(Qt.CursorShape.PointingHandCursor)
        b.clicked.connect(slot)
        return b

    def _on_main(self):
        if self._main_action:
            self.requested.emit(self._main_action, self.task)

    def _on_side(self):
        if self._side_action:
            self.requested.emit(self._side_action, self.task)

    def refresh(self):
        t, st = self.task, self.task.status
        name = t.filename
        self.name.setFullText(name)

        ext = os.path.splitext(name)[1][1:].upper()[:4] or "FILE"
        self.badge.setText(ext)

        self.bar.setValue(int(t.fraction * 1000) if st != "COMPLETED" else 1000)
        bar_state = {"COMPLETED": "done", "FAILED": "bad", "PAUSED": "paused", "QUEUED": "idle",
                     "CANCELLED": "idle"}.get(st, "active")
        if self.bar.property("state") != bar_state:
            self.bar.setProperty("state", bar_state)
            repolish(self.bar)

        pct_kind, meta_kind = "", ""
        parts = []
        if st in ACTIVE_STATES or st == "PAUSED":
            parts.append(f"{format_size(t.downloaded)} of {format_size(t.total)}" if t.total
                         else format_size(t.downloaded))
            if st == "PAUSED":
                parts.append("Paused")
                pct_kind = "warn"
            elif st == "FINALIZING":
                parts.append("Finishing up…")
            elif t.message:
                parts.append(t.message)
            elif t.speed > 0:
                parts.append(f"{format_size(t.speed)}/s")
                if t.total:
                    parts.append(f"{format_eta((t.total - t.downloaded) / t.speed)} left")
            pct_text = f"{int(t.fraction * 100)}%" if t.total else ""
        elif st == "COMPLETED":
            parts.append(format_size(t.total or t.downloaded))
            parts.append(time.strftime("%b %d, %H:%M", time.localtime(t.finished_at or time.time())))
            if not os.path.exists(t.save_path):
                parts.append("File moved or deleted")
            pct_text, pct_kind = "Completed", "ok"
        elif st == "QUEUED":
            parts.append("Waiting in queue")
            pct_text = "Queued"
        elif st == "FAILED":
            parts.append(t.error or "Download failed")
            pct_text, pct_kind, meta_kind = "Failed", "bad", "bad"
        else:
            parts.append("Cancelled")
            pct_text = "Cancelled"
        self.meta.setFullText("  ·  ".join(parts))
        self.pct.setText(pct_text)
        for w, key, val in ((self.pct, "kind", pct_kind), (self.meta, "kind", meta_kind)):
            if w.property(key) != val:
                w.setProperty(key, val)
                repolish(w)

        spec = {
            "DOWNLOADING": ("pause", "pause", "Pause", "cancel", "Cancel download"),
            "QUEUED": ("pause", "pause", "Pause", "cancel", "Cancel download"),
            "PAUSED": ("play", "resume", "Resume", "cancel", "Cancel and discard"),
            "FAILED": ("retry", "retry", "Retry", "remove", "Remove from list"),
            "CANCELLED": ("retry", "retry", "Restart", "remove", "Remove from list"),
            "COMPLETED": ("folder", "folder", "Show in folder", "remove", "Remove from list"),
        }.get(st)
        enabled = spec is not None
        spec = spec or ("pause", "", "", "", "")
        self.btn_main.setIcon(icon(spec[0]))
        self._main_action, self._side_action = spec[1], spec[3]
        self.btn_main.setToolTip(spec[2])
        self.btn_side.setIcon(icon("close"))
        self.btn_side.setToolTip(spec[4])
        self.btn_main.setEnabled(enabled)
        self.btn_side.setEnabled(enabled)

    def mouseDoubleClickEvent(self, event):
        if self.task.status == "COMPLETED":
            self.requested.emit("open", self.task)

    def contextMenuEvent(self, event):
        t, st = self.task, self.task.status
        menu = QMenu(self)
        entries = []
        if st == "COMPLETED":
            entries += [("Open", "open"), ("Show in folder", "folder")]
        if st in ("DOWNLOADING", "QUEUED"):
            entries.append(("Pause", "pause"))
        if st == "PAUSED":
            entries.append(("Resume", "resume"))
        if st in ("FAILED", "CANCELLED"):
            entries.append(("Retry", "retry"))
        entries.append(("Copy link", "copy"))
        for label, action in entries:
            menu.addAction(label).triggered.connect(lambda _=False, a=action: self.requested.emit(a, t))
        menu.addSeparator()
        if st in ("COMPLETED", "FAILED", "CANCELLED"):
            menu.addAction("Remove from list").triggered.connect(lambda: self.requested.emit("remove", t))
        else:
            menu.addAction("Cancel download").triggered.connect(lambda: self.requested.emit("cancel", t))
        if st == "COMPLETED":
            menu.addAction("Delete file from disk").triggered.connect(lambda: self.requested.emit("delete", t))
        menu.exec(event.globalPos())


class Toggle(QCheckBox):
    def __init__(self, checked=False, parent=None):
        super().__init__(parent)
        self.setChecked(checked)
        self.setCursor(Qt.CursorShape.PointingHandCursor)
        self.setFixedSize(36, 20)
        self.toggled.connect(lambda _=False: self.update())

    def hitButton(self, pos):
        return self.rect().contains(pos)

    def paintEvent(self, event):
        p = QPainter(self)
        p.setRenderHint(QPainter.RenderHint.Antialiasing)
        w, h, on = self.width(), self.height(), self.isChecked()
        p.setPen(Qt.PenStyle.NoPen)
        p.setBrush(QColor(C["accent"] if on else C["border2"]))
        p.drawRoundedRect(QRectF(0, 0, w, h), h / 2, h / 2)
        r = h - 6
        p.setBrush(QColor(C["bg"] if on else C["muted"]))
        p.drawEllipse(QRectF(w - 3 - r if on else 3, 3, r, r))
        p.end()


class SettingsDialog(QDialog):
    def __init__(self, cfg, parent=None):
        super().__init__(parent)
        self.setWindowTitle("Settings")
        self.setModal(True)
        self.setFixedWidth(480)
        self.lay = QVBoxLayout(self)
        self.lay.setContentsMargins(28, 26, 28, 22)
        self.lay.setSpacing(0)
        title = QLabel("Settings")
        title.setObjectName("title")
        self.lay.addWidget(title)

        self._section("Downloads")
        self.folder = QLineEdit(cfg["download_folder"])
        self.folder.setObjectName("flat")
        self.folder.setMinimumWidth(190)
        self.folder.setToolTip("Where finished files are saved")
        browse = QPushButton("Change")
        browse.setObjectName("ghost")
        browse.setCursor(Qt.CursorShape.PointingHandCursor)
        browse.clicked.connect(self._browse)
        box = QWidget()
        bl = QHBoxLayout(box)
        bl.setContentsMargins(0, 0, 0, 0)
        bl.setSpacing(0)
        bl.addWidget(self.folder, 1)
        bl.addWidget(browse)
        self._row("Save to", box)

        self.conns = self._spin(1, MAX_SEGMENTS, cfg["connections"])
        self._row("Connections per file", self.conns, "Parallel pieces per download. 1 disables splitting.")
        self.concurrent = self._spin(1, 10, cfg["max_concurrent"])
        self._row("Simultaneous downloads", self.concurrent)
        self.sort = Toggle(bool(cfg["sort_by_type"]))
        self._row("Sort into folders by type", self.sort, "Video, Music, Archives and so on.", line=False)

        self._section("Network")
        self.limit = self._spin(0, 1_000_000, cfg["speed_limit_kb"])
        self.limit.setSingleStep(100)
        self.limit.setSuffix(" KB/s")
        self.limit.setSpecialValueText("Unlimited")
        self.limit.setValue(int(cfg["speed_limit_kb"]))
        self._row("Speed limit", self.limit)

        self.dns = QComboBox()
        for key, label in (("system", "System default"), ("cloudflare", "Cloudflare  1.1.1.1"),
                           ("google", "Google  8.8.8.8"), ("quad9", "Quad9  9.9.9.9")):
            self.dns.addItem(label, key)
        self.dns.setCurrentIndex(max(self.dns.findData(cfg["dns"]), 0))
        if _dns_resolver is None:
            self.dns.setEnabled(False)
            self.dns.setToolTip("Install dnspython to enable custom DNS:  pip install dnspython")
        self._row("DNS", self.dns)
        self.fastest = Toggle(bool(cfg.get("fastest_server", True)))
        self._row("Auto-pick fastest server", self.fastest,
                  "Tests every CDN / mirror a link resolves to and connects to the quickest.", line=False)

        self._section("App")
        self.notify = Toggle(bool(cfg["notifications"]))
        self._row("Notify when a download finishes", self.notify)
        self.sounds = Toggle(bool(cfg.get("sounds", True)))
        self._row("Play sounds", self.sounds, "A chime when a download starts and when it finishes.")
        self.tray = Toggle(bool(cfg["keep_in_tray"]))
        self._row("Keep running in the tray", self.tray, "Closing the window won't stop downloads.", line=False)

        self.lay.addSpacing(26)
        row = QHBoxLayout()
        row.setSpacing(6)
        row.addStretch()
        cancel = QPushButton("Cancel")
        cancel.setObjectName("ghost")
        cancel.setCursor(Qt.CursorShape.PointingHandCursor)
        cancel.clicked.connect(self.reject)
        save = QPushButton("Save")
        save.setObjectName("primary")
        save.setCursor(Qt.CursorShape.PointingHandCursor)
        save.setDefault(True)
        save.clicked.connect(self.accept)
        row.addWidget(cancel)
        row.addWidget(save)
        self.lay.addLayout(row)

    def _section(self, text):
        self.lay.addSpacing(26)
        label = QLabel(text.upper())
        label.setObjectName("section")
        font = label.font()
        font.setLetterSpacing(QFont.SpacingType.AbsoluteSpacing, 1.4)
        label.setFont(font)
        self.lay.addWidget(label)
        self.lay.addSpacing(4)

    def _row(self, label, control, hint="", line=True):
        w = QWidget()
        h = QHBoxLayout(w)
        h.setContentsMargins(0, 11, 0, 11)
        h.setSpacing(16)
        col = QVBoxLayout()
        col.setSpacing(2)
        col.addWidget(QLabel(label))
        if hint:
            hl = QLabel(hint)
            hl.setObjectName("hint")
            hl.setWordWrap(True)
            col.addWidget(hl)
        h.addLayout(col, 1)
        h.addWidget(control, 0, Qt.AlignmentFlag.AlignVCenter)
        self.lay.addWidget(w)
        if line:
            sep = QFrame()
            sep.setObjectName("hairline")
            sep.setFixedHeight(1)
            self.lay.addWidget(sep)

    @staticmethod
    def _spin(lo, hi, value):
        sp = QSpinBox()
        sp.setRange(lo, hi)
        sp.setValue(int(value))
        sp.setAlignment(Qt.AlignmentFlag.AlignRight)
        return sp

    def _browse(self):
        folder = QFileDialog.getExistingDirectory(self, "Select download folder", self.folder.text())
        if folder:
            self.folder.setText(folder)

    def values(self):
        return {"download_folder": self.folder.text().strip() or DEFAULT_CONFIG["download_folder"],
                "connections": self.conns.value(), "max_concurrent": self.concurrent.value(),
                "speed_limit_kb": self.limit.value(), "dns": self.dns.currentData(),
                "fastest_server": self.fastest.isChecked(),
                "sort_by_type": self.sort.isChecked(), "notifications": self.notify.isChecked(),
                "sounds": self.sounds.isChecked(),
                "keep_in_tray": self.tray.isChecked()}


class SoundPlayer:
    CHIMES = {
        "start": ((660.0, 880.0), 0.09),
        "done": ((784.0, 988.0, 1318.0), 0.13),
    }

    def __init__(self):
        import tempfile
        self.dir = os.path.join(tempfile.gettempdir(), "zmanager_sounds")
        self.files = {}
        try:
            os.makedirs(self.dir, exist_ok=True)
            for name, (notes, length) in self.CHIMES.items():
                path = os.path.join(self.dir, f"{name}.wav")
                self._write_wav(path, notes, length)
                self.files[name] = path
        except OSError:
            pass

    @staticmethod
    def _write_wav(path, notes, note_len, rate=44100, volume=0.35):
        import math
        import struct
        import wave
        frames = bytearray()
        for freq in notes:
            n = int(rate * note_len)
            for i in range(n):
                env = min(1.0, i / (rate * 0.005)) * (1 - i / n) ** 1.6
                frames += struct.pack("<h", int(32767 * volume * env * math.sin(2 * math.pi * freq * i / rate)))
        frames += b"\x00\x00" * int(rate * 0.08)
        with wave.open(path, "wb") as w:
            w.setnchannels(1)
            w.setsampwidth(2)
            w.setframerate(rate)
            w.writeframes(bytes(frames))

    def play(self, name):
        path = self.files.get(name)
        if not path:
            return
        try:
            if sys.platform == "win32":
                import winsound
                winsound.PlaySound(path, winsound.SND_FILENAME | winsound.SND_ASYNC | winsound.SND_NODEFAULT)
            elif sys.platform == "darwin":
                subprocess.Popen(["afplay", path])
            else:
                player = shutil.which("paplay") or shutil.which("aplay")
                if player:
                    subprocess.Popen([player, path], stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
                else:
                    QApplication.beep()
        except Exception:
            pass


FILTERS = (("all", "All"), ("active", "Active"), ("done", "Completed"), ("failed", "Failed"))


def matches(task, flt):
    s = task.status
    if flt == "active":
        return s in ("QUEUED", "DOWNLOADING", "FINALIZING", "PAUSED")
    if flt == "done":
        return s == "COMPLETED"
    if flt == "failed":
        return s in ("FAILED", "CANCELLED")
    return True


class MainWindow(QMainWindow):
    bridge_request = pyqtSignal(object)
    bridge_status = pyqtSignal(bool, str)
    bridge_handoff = pyqtSignal(str)

    def __init__(self):
        super().__init__()
        self.setWindowTitle(APP_NAME)
        self.resize(780, 680)
        self.setMinimumSize(620, 480)
        self.setAcceptDrops(True)

        self.cfg = dict(DEFAULT_CONFIG)
        saved = load_json(CONFIG_FILE, {})
        if isinstance(saved, dict):
            self.cfg.update({k: v for k, v in saved.items() if k in DEFAULT_CONFIG})
        self.limiter = RateLimiter()
        self._apply_runtime_config()

        self.tasks, self.cards = [], {}
        self.filter = "all"
        self._quitting = self._dirty = self._tray_hint_shown = self._titlebar_done = False
        self._bridge_text, self._bridge_ok = "Starting…", None
        self.sounds = SoundPlayer()

        self._build_ui()
        self._build_tray()
        self._load_state()
        self.apply_filter()

        self.bridge_request.connect(self._on_bridge_request)
        self.bridge_status.connect(self._on_bridge_status)
        self.bridge_handoff.connect(self._on_bridge_handoff)
        self.bridge = BridgeServer(self.bridge_request.emit, self.bridge_status.emit,
                                   on_handoff=self.bridge_handoff.emit)
        self.bridge.start()

        self.timer = QTimer(self)
        self.timer.timeout.connect(self._tick)
        self.timer.start(1000)

    def _build_ui(self):
        central = QWidget()
        central.setObjectName("central")
        self.setCentralWidget(central)
        root = QVBoxLayout(central)
        root.setContentsMargins(28, 22, 28, 14)
        root.setSpacing(16)

        head = QHBoxLayout()
        head.setSpacing(12)
        logo = QLabel()
        pm = make_logo(48, tile=False)
        pm.setDevicePixelRatio(2.0)
        logo.setPixmap(pm)
        logo.setFixedSize(24, 24)
        title = QLabel(APP_NAME)
        title.setObjectName("title")
        head.addWidget(logo)
        head.addWidget(title)
        head.addStretch()
        btn_settings = self._icon_button("settings", "Settings", self.open_settings)
        head.addWidget(btn_settings)
        root.addLayout(head)

        add = QHBoxLayout()
        add.setSpacing(10)
        self.url_input = QLineEdit()
        self.url_input.setPlaceholderText("Paste a link")
        self.url_input.returnPressed.connect(self.add_from_input)
        btn_add = QPushButton("Add")
        btn_add.setObjectName("primary")
        btn_add.setCursor(Qt.CursorShape.PointingHandCursor)
        btn_add.clicked.connect(self.add_from_input)
        add.addWidget(self.url_input, 1)
        add.addWidget(btn_add)
        root.addLayout(add)

        bar = QHBoxLayout()
        bar.setSpacing(4)
        group = QButtonGroup(self)
        group.setExclusive(True)
        self.pills = {}
        for key, label in FILTERS:
            b = QPushButton(label)
            b.setObjectName("pill")
            b.setCheckable(True)
            b.setCursor(Qt.CursorShape.PointingHandCursor)
            b.setChecked(key == "all")
            b.clicked.connect(lambda _=False, k=key: self._set_filter(k))
            group.addButton(b)
            bar.addWidget(b)
            self.pills[key] = b
        bar.addStretch()
        self.search = QLineEdit()
        self.search.setObjectName("search")
        self.search.setPlaceholderText("Search")
        self.search.setClearButtonEnabled(True)
        self.search.addAction(icon("search"), QLineEdit.ActionPosition.LeadingPosition)
        self.search.setMaximumWidth(190)
        self.search.textChanged.connect(self.apply_filter)
        bar.addWidget(self.search)
        bar.addSpacing(6)
        bar.addWidget(self._icon_button("pause", "Pause all", self.pause_all))
        bar.addWidget(self._icon_button("play", "Resume all", self.resume_all))
        bar.addWidget(self._icon_button("done", "Clear completed", self.clear_completed))
        root.addLayout(bar)

        self.scroll = QScrollArea()
        self.scroll.setWidgetResizable(True)
        self.scroll.setFrameShape(QFrame.Shape.NoFrame)
        self.scroll.setHorizontalScrollBarPolicy(Qt.ScrollBarPolicy.ScrollBarAlwaysOff)
        self.scroll.viewport().setAutoFillBackground(False)
        container = QWidget()
        container.setObjectName("taskList")
        self.list_layout = QVBoxLayout(container)
        self.list_layout.setContentsMargins(0, 0, 6, 8)
        self.list_layout.setSpacing(8)
        self.list_layout.setAlignment(Qt.AlignmentFlag.AlignTop)

        self.empty = QWidget()
        el = QVBoxLayout(self.empty)
        el.setContentsMargins(0, 90, 0, 0)
        el.setSpacing(6)
        self.empty_title = QLabel("No downloads yet")
        self.empty_title.setObjectName("emptyTitle")
        self.empty_hint = QLabel("Paste a link above, drop one here, or download something in Edge.")
        self.empty_hint.setObjectName("muted")
        for w in (self.empty_title, self.empty_hint):
            w.setAlignment(Qt.AlignmentFlag.AlignCenter)
            el.addWidget(w)
        self.list_layout.addWidget(self.empty)
        self.scroll.setWidget(container)
        root.addWidget(self.scroll, 1)

        foot = QHBoxLayout()
        foot.setSpacing(8)
        self.dot = QLabel()
        self.dot.setObjectName("dot")
        self.status_label = QLabel(self._bridge_text)
        self.status_label.setObjectName("footer")
        self.speed_label = QLabel("Idle")
        self.speed_label.setObjectName("footer")
        foot.addWidget(self.dot)
        foot.addWidget(self.status_label)
        foot.addStretch()
        foot.addWidget(self.speed_label)
        root.addLayout(foot)

    def _icon_button(self, kind, tip, slot):
        b = QToolButton()
        b.setIcon(icon(kind))
        b.setIconSize(QSize(18, 18))
        b.setFixedSize(34, 34)
        b.setToolTip(tip)
        b.setCursor(Qt.CursorShape.PointingHandCursor)
        b.clicked.connect(slot)
        return b

    def _build_tray(self):
        self.tray = None
        if not QSystemTrayIcon.isSystemTrayAvailable():
            return
        self.tray = QSystemTrayIcon(QIcon(make_logo(64)), self)
        self.tray.setToolTip(APP_NAME)
        self.tray_menu = QMenu()
        self.tray_menu.addAction("Show Z-Manager").triggered.connect(self.show_window)
        self.tray_menu.addAction("Pause all").triggered.connect(self.pause_all)
        self.tray_menu.addAction("Resume all").triggered.connect(self.resume_all)
        self.tray_menu.addSeparator()
        self.tray_menu.addAction("Quit").triggered.connect(self.quit_app)
        self.tray.setContextMenu(self.tray_menu)
        self.tray.activated.connect(
            lambda reason: self.show_window() if reason == QSystemTrayIcon.ActivationReason.Trigger else None)
        self.tray.show()

    def showEvent(self, event):
        super().showEvent(event)
        if sys.platform == "win32" and not self._titlebar_done:
            self._titlebar_done = True
            try:
                import ctypes
                hwnd = int(self.winId())
                dwm = ctypes.windll.dwmapi
                for attr, value in ((20, 1), (19, 1), (35, 0x0A0A0A)):
                    v = ctypes.c_int(value)
                    dwm.DwmSetWindowAttribute(hwnd, attr, ctypes.byref(v), ctypes.sizeof(v))
            except Exception:
                pass

    def show_window(self):
        self.showNormal()
        self.raise_()
        self.activateWindow()

    def pop_up(self):
        self.setWindowState(self.windowState() & ~Qt.WindowState.WindowMinimized)
        self.show()
        self.raise_()
        self.activateWindow()
        if sys.platform == "win32":
            try:
                import ctypes
                user32 = ctypes.windll.user32
                hwnd = ctypes.c_void_p(int(self.winId()))
                flags = 0x0001 | 0x0002 | 0x0040
                user32.SetWindowPos(hwnd, ctypes.c_void_p(-1), 0, 0, 0, 0, flags)
                user32.SetWindowPos(hwnd, ctypes.c_void_p(-2), 0, 0, 0, 0, flags)
                user32.SetForegroundWindow(hwnd)
            except Exception:
                pass

    def _play(self, name):
        if self.cfg.get("sounds", True):
            self.sounds.play(name)

    def closeEvent(self, event):
        if not self._quitting and self.tray and self.cfg["keep_in_tray"]:
            event.ignore()
            self.hide()
            if not self._tray_hint_shown:
                self._tray_hint_shown = True
                self.tray.showMessage(APP_NAME, "Still running in the tray. Right-click the icon to quit.",
                                      QSystemTrayIcon.MessageIcon.Information, 3000)
            return
        event.accept()
        self.quit_app()

    def quit_app(self):
        if self._quitting:
            return
        self._quitting = True
        self.bridge.shutdown()
        running = [t for t in self.tasks if t.worker_alive]
        for t in running:
            t.worker.pause()
        deadline = time.time() + 5
        for t in running:
            t.worker.join(max(deadline - time.time(), 0.1))
        self._save_state()
        if self.tray:
            self.tray.hide()
        QApplication.quit()

    def dragEnterEvent(self, event):
        if event.mimeData().hasUrls() or event.mimeData().hasText():
            event.acceptProposedAction()

    def dropEvent(self, event):
        md = event.mimeData()
        urls = [u.toString() for u in md.urls() if u.scheme() in ("http", "https")]
        if not urls and md.hasText():
            urls = re.findall(r"https?://\S+", md.text())
        for u in urls:
            self.add_download(u)
        if urls:
            event.acceptProposedAction()

    def _apply_runtime_config(self):
        self.limiter.set_rate(int(self.cfg["speed_limit_kb"]) * 1024)
        set_dns_server(DNS_SERVERS.get(self.cfg["dns"]))
        set_fastest_server(self.cfg.get("fastest_server", True))

    def open_settings(self):
        dlg = SettingsDialog(self.cfg, self)
        if dlg.exec() == QDialog.DialogCode.Accepted:
            self.cfg.update(dlg.values())
            save_json(CONFIG_FILE, self.cfg)
            self._apply_runtime_config()
            self.pump()
            self.flash("Settings saved")

    def _on_bridge_request(self, payload):
        task = self.add_download(payload["url"], payload.get("referrer", ""), payload.get("filename", ""),
                                 payload.get("cookies"), payload.get("userAgent", ""), payload.get("id"))
        if task is None and payload.get("id"):
            self.bridge.statuses[payload["id"]] = "GONE"
        if task:
            self.pop_up()

    def _on_bridge_handoff(self, task_id):
        task = next((t for t in self.tasks if t.id == task_id), None)
        if task and task.status == "FAILED":
            name = task.filename
            self.remove_task(task)
            self.flash(f"Sent to browser: {name}", 5000)

    def _on_bridge_status(self, ok, text):
        self._bridge_ok, self._bridge_text = ok, text
        self.dot.setProperty("ok", "true" if ok else "false")
        repolish(self.dot)
        self.status_label.setText(text)

    def flash(self, text, ms=3000):
        self.status_label.setText(text)
        QTimer.singleShot(ms, lambda: self.status_label.setText(self._bridge_text))

    def add_from_input(self):
        text = self.url_input.text().strip()
        urls = re.findall(r"https?://[^\s]+", text)
        if not urls and text and " " not in text and "." in text:
            urls = ["https://" + text]
        if not urls:
            self.flash("That doesn't look like a link")
            return
        for u in urls:
            self.add_download(u)
        self.url_input.clear()

    def _taken(self, exclude=None):
        return {os.path.normcase(t.save_path) for t in list(self.tasks) if t is not exclude}

    def add_download(self, url, referrer="", hint="", cookies=None, user_agent="", task_id=None):
        dup = next((t for t in self.tasks if t.url == url and t.status not in ("COMPLETED", "FAILED", "CANCELLED")), None)
        if dup:
            self.flash("That download is already in your list")
            return None
        name = (sanitize_filename(hint) or sanitize_filename(unquote(os.path.basename(urlparse(url).path)))
                or f"download_{int(time.time())}")
        folder = self.cfg["download_folder"]
        if self.cfg["sort_by_type"]:
            cat = category_of(name)
            if cat != "Other":
                folder = os.path.join(folder, cat)
        path = unique_path(os.path.join(folder, name), lambda p: os.path.normcase(p) in self._taken())
        task = DownloadTask({"id": task_id or uuid.uuid4().hex[:12], "url": url, "save_path": path,
                             "status": "QUEUED", "referrer": referrer, "added": time.time(),
                             "cookies": cookies or [], "user_agent": user_agent})
        self._register(task)
        self._save_state()
        self._play("start")
        self.pump()
        self.apply_filter()
        return task

    def _register(self, task):
        card = TaskCard(task)
        card.requested.connect(self.on_card_request)
        task.status_changed.connect(self._on_status_changed)
        task.changed.connect(self._mark_dirty)
        self.tasks.insert(0, task)
        self.cards[task.id] = card
        self.list_layout.insertWidget(1, card)

    def pump(self):
        active = sum(1 for t in self.tasks if t.active)
        for t in reversed(self.tasks):
            if active >= int(self.cfg["max_concurrent"]):
                break
            if t.status == "QUEUED":
                t.start(self.cfg, self.limiter, lambda p, t=t: os.path.normcase(p) in self._taken(t))
                if t.active:
                    active += 1

    def _on_status_changed(self, task):
        if task not in self.tasks:
            return
        self.bridge.statuses[task.id] = task.status
        self._save_state()
        self.pump()
        self.apply_filter()
        if task.status == "COMPLETED":
            self._play("done")
        if task.status in ("COMPLETED", "FAILED") and self.tray and self.cfg["notifications"]:
            if task.status == "COMPLETED":
                self.tray.showMessage("Download complete", task.filename, QSystemTrayIcon.MessageIcon.Information, 4000)
            else:
                self.tray.showMessage("Download failed", f"{task.filename}\n{task.error}",
                                      QSystemTrayIcon.MessageIcon.Warning, 5000)

    def on_card_request(self, action, task):
        if task not in self.tasks:
            return
        if action == "pause":
            task.pause()
        elif action in ("resume", "retry"):
            task.queue()
            self.pump()
        elif action == "cancel":
            if task.downloaded > 0 and QMessageBox.question(
                    self, "Cancel download", f"Discard the {format_size(task.downloaded)} already downloaded?",
                    QMessageBox.StandardButton.Yes | QMessageBox.StandardButton.No,
                    QMessageBox.StandardButton.No) != QMessageBox.StandardButton.Yes:
                return
            task.cancel()
        elif action == "remove":
            self.remove_task(task)
        elif action == "delete":
            if QMessageBox.question(self, "Delete file", f"Permanently delete “{task.filename}” from disk?",
                                    QMessageBox.StandardButton.Yes | QMessageBox.StandardButton.No,
                                    QMessageBox.StandardButton.No) == QMessageBox.StandardButton.Yes:
                self.remove_task(task, delete_file=True)
        elif action == "open":
            if os.path.exists(task.save_path):
                QDesktopServices.openUrl(QUrl.fromLocalFile(task.save_path))
            else:
                self.flash("File not found. It was moved or deleted")
        elif action == "folder":
            self._reveal(task.save_path)
        elif action == "copy":
            QApplication.clipboard().setText(task.url)
            self.flash("Link copied")

    def _reveal(self, path):
        folder = os.path.dirname(path)
        try:
            if sys.platform == "win32" and os.path.exists(path):
                subprocess.Popen(["explorer", "/select,", os.path.normpath(path)])
            elif sys.platform == "darwin" and os.path.exists(path):
                subprocess.Popen(["open", "-R", path])
            else:
                QDesktopServices.openUrl(QUrl.fromLocalFile(folder))
        except OSError:
            QDesktopServices.openUrl(QUrl.fromLocalFile(folder))

    def remove_task(self, task, delete_file=False):
        if task.worker_alive:
            task.worker.cancel()
        if task.status != "COMPLETED":
            remove_parts(task.save_path)
        if delete_file:
            try:
                os.remove(task.save_path)
            except OSError:
                pass
        self.tasks.remove(task)
        self.bridge.statuses.pop(task.id, None)
        card = self.cards.pop(task.id, None)
        if card:
            self.list_layout.removeWidget(card)
            card.deleteLater()
        self._save_state()
        self.apply_filter()

    def pause_all(self):
        for t in self.tasks:
            if t.status in ("DOWNLOADING", "QUEUED"):
                t.pause()

    def resume_all(self):
        for t in reversed(self.tasks):
            if t.status == "PAUSED":
                t.queue()
        self.pump()

    def clear_completed(self):
        for t in [t for t in self.tasks if t.status == "COMPLETED"]:
            self.remove_task(t)

    def _set_filter(self, key):
        self.filter = key
        self.apply_filter()

    def apply_filter(self, *_):
        q = self.search.text().strip().lower()
        shown = 0
        for t in self.tasks:
            ok = matches(t, self.filter) and (not q or q in t.filename.lower() or q in t.url.lower())
            self.cards[t.id].setVisible(ok)
            shown += ok
        for key, label in FILTERS:
            n = sum(1 for t in self.tasks if matches(t, key))
            self.pills[key].setText(f"{label}  {n}" if n else label)
        self.empty.setVisible(shown == 0)
        if not self.tasks:
            self.empty_title.setText("No downloads yet")
            self.empty_hint.setText("Paste a link above, drop one here, or download something in Edge.")
        else:
            self.empty_title.setText("Nothing here")
            self.empty_hint.setText("No downloads match this filter.")

    def _tick(self):
        self.pump()
        active = [t for t in self.tasks if t.active]
        speed = sum(t.speed for t in active)
        if active:
            self.speed_label.setText(f"{format_size(speed)}/s  |  {len(active)} active")
        else:
            queued = sum(1 for t in self.tasks if t.status == "QUEUED")
            self.speed_label.setText(f"{queued} queued" if queued else "Idle")
        if self.tray:
            self.tray.setToolTip(f"{APP_NAME} - {format_size(speed)}/s" if active else APP_NAME)
        if self._dirty:
            self._save_state()

    def _mark_dirty(self):
        self._dirty = True

    def _save_state(self):
        self._dirty = False
        save_json(STATE_FILE, {t.id: t.to_dict() for t in reversed(self.tasks)})

    def _load_state(self):
        data = load_json(STATE_FILE, {})
        if not isinstance(data, dict):
            return
        for tid, d in data.items():
            try:
                path = d["save_path"]
                status = str(d.get("status", "PAUSED")).upper()
                error = d.get("error", "")
                if status in ("DOWNLOADING", "QUEUED", "FINALIZING"):
                    status = "PAUSED"
                elif status.startswith("ERROR"):
                    status, error = "FAILED", status.split(":", 1)[-1].strip().capitalize()
                elif status not in VALID_STATES:
                    status = "FAILED"
                segments, downloaded = int(d.get("segments", 0) or 0), int(d.get("downloaded", 0) or 0)
                if status == "PAUSED":
                    if not has_parts(path) and os.path.exists(path) and os.path.getsize(path) > 0:
                        os.replace(path, part_path(path, 0))
                        segments = 1
                    downloaded = sum(os.path.getsize(part_path(path, i)) for i in range(MAX_SEGMENTS)
                                     if os.path.exists(part_path(path, i)))
                task = DownloadTask({**d, "id": str(tid), "status": status, "error": error,
                                     "segments": segments, "downloaded": downloaded})
                self._register(task)
            except (KeyError, OSError, ValueError, TypeError):
                continue


def main():
    app = QApplication(sys.argv)
    app.setApplicationName(APP_NAME)
    app.setQuitOnLastWindowClosed(False)
    app.setStyleSheet(build_qss())
    app.setWindowIcon(QIcon(make_logo(64)))
    win = MainWindow()
    if "--background" not in sys.argv:
        win.show()
    sys.exit(app.exec())


if __name__ == "__main__":
    main()