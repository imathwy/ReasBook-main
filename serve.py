#!/usr/bin/env python3
"""Serve ReasBook pages locally with the generated Project Pages prefix."""

import argparse
import os
import re
from http import HTTPStatus
from http.server import HTTPServer, SimpleHTTPRequestHandler
from urllib.parse import unquote, urlparse

BOOK_SITE = os.path.abspath("./ReasBookWeb/_site")
DOCS_SITE = os.path.abspath("./ReasBook/.lake/build/doc")
SECTIONS_LEAN = os.path.abspath("./ReasBookWeb/ReasBookSite/Sections.lean")


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
            local_docs = os.path.join(DOCS_SITE, rel)
            if os.path.exists(local_docs):
                return local_docs
            site_docs = os.path.join(BOOK_SITE, "docs", rel)
            if os.path.exists(site_docs):
                return site_docs
            return local_docs

        if req_path.startswith(SITE_ROOT):
            rel = req_path[len(SITE_ROOT) :]
            return os.path.join(BOOK_SITE, rel)

        # Allow unprefixed local routes such as /books/... and /papers/... to
        # make manually-authored links work in local preview.
        if req_path.startswith(("/books/", "/papers/", "/static/", "/index.html")):
            rel = req_path.lstrip("/")
            return os.path.join(BOOK_SITE, rel)

        # Return a non-existing path so the base handler responds with 404
        # instead of raising an exception traceback.
        return os.path.join(BOOK_SITE, "__not_found__")


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("port", type=int, nargs="?", default=8000)
    args = parser.parse_args()

    with HTTPServer(("", args.port), ReasBookHandler) as httpd:
        print(f"Serving at http://localhost:{args.port}{SITE_ROOT}")
        print(f"{SITE_ROOT} -> {BOOK_SITE}")
        print(f"{SITE_ROOT}docs/ -> {DOCS_SITE} (fallback: {os.path.join(BOOK_SITE, 'docs')})")
        httpd.serve_forever()


if __name__ == "__main__":
    main()
