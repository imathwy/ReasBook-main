#!/usr/bin/env python3
"""Serve ReasBook pages locally with the generated Project Pages prefix."""

import argparse
import os
from pathlib import Path
import re
from http import HTTPStatus
from http.server import HTTPServer, SimpleHTTPRequestHandler
from urllib.parse import unquote, urlparse

ROOT_DIR = Path(__file__).resolve().parents[2]
BOOK_SITE = os.path.abspath(os.environ.get("REASBOOK_SITE_DIR", ROOT_DIR / "ReasBookWeb" / "_site"))
DOCS_SITE = os.path.abspath(os.environ.get("REASBOOK_DOC_SOURCE", ROOT_DIR / "ReasBook" / ".lake" / "build" / "doc"))
SECTIONS_LEAN = os.path.abspath(os.environ.get("REASBOOK_SECTIONS_FILE", ROOT_DIR / "ReasBookWeb" / "ReasBookSite" / "Sections.lean"))


def _normalize_site_root(value: str) -> str:
    v = value.strip()
    if not v:
        return "/ReasBook/"
    if not v.startswith("/"):
        v = "/" + v
    if not v.endswith("/"):
        v = v + "/"
    return v


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


def _safe_join(root: str, relative: str) -> str:
    """Resolve a request below ``root`` without permitting ``..`` escapes."""

    root_path = Path(root).resolve()
    candidate = (root_path / relative.lstrip("/")).resolve()
    if candidate == root_path or root_path in candidate.parents:
        return str(candidate)
    return str(root_path / "__not_found__")


class ReasBookHandler(SimpleHTTPRequestHandler):
    def do_GET(self):
        if self.path == "/favicon.ico":
            self.send_response(HTTPStatus.NO_CONTENT)
            self.end_headers()
            return
        if self.path == "/":
            self.send_response(HTTPStatus.MOVED_PERMANENTLY)
            self.send_header("Location", SITE_ROOT)
            self.end_headers()
            return
        super().do_GET()

    def translate_path(self, path: str) -> str:
        parsed = urlparse(path)
        req_path = unquote(parsed.path)

        if req_path.startswith(f"{SITE_ROOT}docs/") or req_path.startswith("/docs/"):
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
        if req_path.startswith(("/books/", "/papers/", "/static/", "/index.html")):
            rel = req_path.lstrip("/")
            return _safe_join(BOOK_SITE, rel)

        # Return a non-existing path so the base handler responds with 404
        # instead of raising an exception traceback.
        return os.path.join(BOOK_SITE, "__not_found__")


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("port", type=int, nargs="?", default=8000)
    parser.add_argument("--host", default=os.environ.get("REASBOOK_SERVE_HOST", "127.0.0.1"))
    parser.add_argument("--site-root", default=os.environ.get("REASBOOK_SITE_ROOT", ""))
    args = parser.parse_args()

    global SITE_ROOT
    if args.site_root:
        SITE_ROOT = _normalize_site_root(args.site_root)

    with HTTPServer((args.host, args.port), ReasBookHandler) as httpd:
        print(f"Serving at http://localhost:{args.port}{SITE_ROOT}")
        print(f"{SITE_ROOT} -> {BOOK_SITE}")
        print(f"{SITE_ROOT}docs/ -> {DOCS_SITE} (fallback: {os.path.join(BOOK_SITE, 'docs')})")
        httpd.serve_forever()


if __name__ == "__main__":
    main()
