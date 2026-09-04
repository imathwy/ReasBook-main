#!/usr/bin/env python3
"""Serve ReasBook pages locally with the generated Project Pages prefix."""

import argparse
from io import BytesIO
import json
import os
from pathlib import Path
import re
import stat
from http import HTTPStatus
from http.server import SimpleHTTPRequestHandler, ThreadingHTTPServer
from urllib.parse import unquote, urlparse
import uuid

ROOT_DIR = Path(__file__).resolve().parents[2]
BOOK_SITE = os.path.abspath(
    os.environ.get("REASBOOK_SITE_DIR", ROOT_DIR / "ReasBookWeb" / "_site")
)
DOCS_SITE = os.path.abspath(
    os.environ.get(
        "REASBOOK_DOC_SOURCE", ROOT_DIR / "ReasBook" / ".lake" / "build" / "doc"
    )
)
SECTIONS_LEAN = os.path.abspath(
    os.environ.get(
        "REASBOOK_SECTIONS_FILE",
        ROOT_DIR / "ReasBookWeb" / "ReasBookSite" / "Sections.lean",
    )
)


def _normalize_site_root(value: str) -> str:
    v = value.strip()
    if not v:
        return "/ReasBook/"
    if not v.startswith("/"):
        v = "/" + v
    if not v.endswith("/"):
        v = v + "/"
    return v


def _normalize_public_prefix(value: str) -> str:
    """Normalize an explicit reverse-proxy path without accepting a URL."""

    prefix = value.strip()
    if not prefix or prefix == "/":
        return ""
    if not prefix.startswith("/"):
        prefix = "/" + prefix
    prefix = prefix.rstrip("/")
    parsed = urlparse(prefix)
    if (
        parsed.scheme
        or parsed.netloc
        or parsed.params
        or parsed.query
        or parsed.fragment
        or "\\" in prefix
        or any(ord(char) < 32 for char in prefix)
        or any(part in {"", ".", ".."} for part in prefix.split("/")[1:])
    ):
        raise ValueError("public prefix must be a normalized absolute URL path")
    return prefix


def _safe_ready_file_path(value: Path) -> Path:
    """Prepare a lexical output path without following symbolic links."""

    target = Path(os.path.abspath(os.fspath(Path(value).expanduser())))

    def reject_link_components() -> None:
        for component in (target, *target.parents):
            try:
                metadata = component.lstat()
            except FileNotFoundError:
                continue
            except OSError as exc:
                raise ValueError(
                    f"cannot inspect ready-file path component: {component}"
                ) from exc
            if stat.S_ISLNK(metadata.st_mode):
                raise ValueError(
                    "ready-file path contains a symbolic-link component: "
                    f"{component}"
                )

    reject_link_components()
    target.parent.mkdir(parents=True, exist_ok=True)
    # Recheck after creating missing parents so a newly materialized component
    # cannot silently change the destination before the atomic replace.
    reject_link_components()
    return target


def detect_site_root() -> str:
    env_root = os.environ.get("REASBOOK_SITE_ROOT")
    if env_root:
        return _normalize_site_root(env_root)

    if os.path.exists(SECTIONS_LEAN):
        with open(SECTIONS_LEAN, "r", encoding="utf-8") as f:
            content = f.read()
        m = re.search(r'def siteRoot : String := "([^"]+)"', content)
        if m:
            return _normalize_site_root(m.group(1))

    return "/ReasBook/"


SITE_ROOT = detect_site_root()
PUBLIC_PREFIX = _normalize_public_prefix(os.environ.get("REASBOOK_PUBLIC_PREFIX", ""))
ROUTING_MODES = ("compat", "strict")
ROUTING_MODE = "compat"


def _public_site_root() -> str:
    return PUBLIC_PREFIX + SITE_ROOT


def _strip_public_prefix(path: str) -> str:
    if PUBLIC_PREFIX and path == PUBLIC_PREFIX:
        return "/"
    if PUBLIC_PREFIX and path.startswith(PUBLIC_PREFIX + "/"):
        return path[len(PUBLIC_PREFIX) :]
    return path


def _rewrite_site_root(payload: bytes) -> bytes:
    """Prefix root-relative site URLs without touching module path segments."""

    if not PUBLIC_PREFIX:
        return payload
    pattern = re.compile(
        rb"(?<![A-Za-z0-9._~%/-])" + re.escape(SITE_ROOT.encode("utf-8"))
    )
    return pattern.sub(_public_site_root().encode("utf-8"), payload)


def _safe_join(root: str, relative: str) -> str:
    """Resolve a request below ``root`` without permitting ``..`` escapes."""

    root_path = Path(root).resolve()
    candidate = (root_path / relative.lstrip("/")).resolve()
    if candidate == root_path or root_path in candidate.parents:
        return str(candidate)
    return str(root_path / "__not_found__")


class ReasBookHandler(SimpleHTTPRequestHandler):
    def _handle_special_request(self) -> bool:
        public_path = unquote(urlparse(self.path).path)
        request_path = _strip_public_prefix(public_path)
        if ROUTING_MODE == "compat" and request_path == "/favicon.ico":
            self.send_response(HTTPStatus.NO_CONTENT)
            self.end_headers()
            return True
        if request_path == "/":
            target = _public_site_root()
            # A root-mounted site must serve ``/`` directly.  With a public
            # proxy prefix, redirect only until the externally visible root is
            # reached; redirecting that target to itself creates an infinite
            # loop.
            if public_path != target:
                self.send_response(HTTPStatus.PERMANENT_REDIRECT)
                self.send_header("Location", target)
                self.send_header("Content-Length", "0")
                self.end_headers()
                return True
        site_root_without_slash = SITE_ROOT.rstrip("/")
        if site_root_without_slash and request_path == site_root_without_slash:
            self.send_response(HTTPStatus.PERMANENT_REDIRECT)
            self.send_header("Location", _public_site_root())
            self.send_header("Content-Length", "0")
            self.end_headers()
            return True
        return False

    def do_GET(self):
        if self._handle_special_request():
            return
        super().do_GET()

    def do_HEAD(self):
        if self._handle_special_request():
            return
        super().do_HEAD()

    def send_head(self):
        """Rewrite the generated site root only for explicit path proxies."""

        if not PUBLIC_PREFIX:
            return super().send_head()

        path = self.translate_path(self.path)
        if os.path.isdir(path):
            if not urlparse(self.path).path.endswith("/"):
                return super().send_head()
            for name in ("index.html", "index.htm"):
                candidate = os.path.join(path, name)
                if os.path.isfile(candidate):
                    path = candidate
                    break
            else:
                return super().send_head()

        content_type = self.guess_type(path)
        textual = content_type.startswith("text/") or content_type in {
            "application/javascript",
            "application/json",
            "application/xml",
        }
        if not textual:
            return super().send_head()

        try:
            source = Path(path)
            payload = _rewrite_site_root(source.read_bytes())
        except OSError:
            self.send_error(HTTPStatus.NOT_FOUND, "File not found")
            return None

        self.send_response(HTTPStatus.OK)
        self.send_header("Content-type", content_type)
        self.send_header("Content-Length", str(len(payload)))
        self.send_header(
            "Last-Modified",
            self.date_time_string(source.stat().st_mtime),
        )
        self.end_headers()
        return BytesIO(payload)

    def translate_path(self, path: str) -> str:
        parsed = urlparse(path)
        req_path = _strip_public_prefix(unquote(parsed.path))

        if ROUTING_MODE == "compat" and (
            req_path.startswith(f"{SITE_ROOT}docs/") or req_path.startswith("/docs/")
        ):
            rel = req_path.split("/docs/", 1)[1]
            local_docs = _safe_join(DOCS_SITE, rel)
            if os.path.exists(local_docs):
                return local_docs
            site_docs = _safe_join(BOOK_SITE, os.path.join("docs", rel))
            if os.path.exists(site_docs):
                return site_docs
            return local_docs

        if req_path.startswith(SITE_ROOT):
            rel = req_path[len(SITE_ROOT) :]
            return _safe_join(BOOK_SITE, rel)

        # Allow unprefixed local routes such as /books/... and /papers/... to
        # make manually-authored links work in local preview.
        if ROUTING_MODE == "compat" and req_path.startswith(
            ("/books/", "/papers/", "/static/", "/index.html")
        ):
            rel = req_path.lstrip("/")
            return _safe_join(BOOK_SITE, rel)

        # Return a non-existing path so the base handler responds with 404
        # instead of raising an exception traceback.
        return os.path.join(BOOK_SITE, "__not_found__")


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("port", type=int, nargs="?", default=8000)
    parser.add_argument(
        "--host", default=os.environ.get("REASBOOK_SERVE_HOST", "127.0.0.1")
    )
    parser.add_argument("--site-root", default=os.environ.get("REASBOOK_SITE_ROOT", ""))
    parser.add_argument(
        "--public-prefix",
        default=os.environ.get("REASBOOK_PUBLIC_PREFIX", ""),
        help="external path stripped by a reverse proxy (for example /proxy/3000)",
    )
    parser.add_argument(
        "--routing-mode",
        choices=ROUTING_MODES,
        default=os.environ.get("REASBOOK_ROUTING_MODE", "compat"),
        help=(
            "compat keeps unprefixed development aliases; strict matches the "
            "production base-path boundary"
        ),
    )
    parser.add_argument(
        "--ready-file",
        type=Path,
        help="atomically write the bound origin and URL after the socket is ready",
    )
    args = parser.parse_args()

    global PUBLIC_PREFIX, ROUTING_MODE, SITE_ROOT
    if args.site_root:
        SITE_ROOT = _normalize_site_root(args.site_root)
    ROUTING_MODE = args.routing_mode
    try:
        PUBLIC_PREFIX = _normalize_public_prefix(args.public_prefix)
    except ValueError as exc:
        parser.error(str(exc))

    ready_file = None
    if args.ready_file is not None:
        try:
            ready_file = _safe_ready_file_path(args.ready_file)
        except ValueError as exc:
            parser.error(str(exc))

    with ThreadingHTTPServer((args.host, args.port), ReasBookHandler) as httpd:
        bound_port = int(httpd.server_address[1])
        origin = f"http://127.0.0.1:{bound_port}"
        url = origin + _public_site_root()
        if ready_file is not None:
            temporary = ready_file.with_name(
                f".{ready_file.name}.{uuid.uuid4().hex}.tmp"
            )
            temporary.write_text(
                json.dumps({"origin": origin, "url": url}) + "\n",
                encoding="utf-8",
            )
            os.replace(temporary, ready_file)
        print(f"Serving at {url}")
        print(f"{SITE_ROOT} -> {BOOK_SITE}")
        print(f"routing mode: {ROUTING_MODE}")
        if PUBLIC_PREFIX:
            print(f"reverse-proxy prefix: {PUBLIC_PREFIX}")
        if ROUTING_MODE == "compat":
            print(
                f"{SITE_ROOT}docs/ -> {DOCS_SITE} "
                f"(fallback: {os.path.join(BOOK_SITE, 'docs')})"
            )
        else:
            print(f"{SITE_ROOT}docs/ -> {os.path.join(BOOK_SITE, 'docs')} " "(strict)")
        try:
            httpd.serve_forever()
        except KeyboardInterrupt:
            pass


if __name__ == "__main__":
    main()
