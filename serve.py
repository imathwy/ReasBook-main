#!/usr/bin/env python3
"""Serve ReasBook pages locally with the Project Pages prefix /ReasBook-main/."""

import argparse
import os
from http import HTTPStatus
from http.server import HTTPServer, SimpleHTTPRequestHandler
from urllib.parse import unquote, urlparse

SITE_ROOT = "/ReasBook-main/"
LEGACY_SITE_ROOT = "/ReasBook/"
BOOK_SITE = os.path.abspath("./ReasBookWeb/_site")
DOCS_SITE = os.path.abspath("./ReasBook/.lake/build/doc")


class ReasBookHandler(SimpleHTTPRequestHandler):
    def do_GET(self):
        parsed = urlparse(self.path)
        req_path = unquote(parsed.path)

        if req_path == "/favicon.ico":
            self.send_response(HTTPStatus.NO_CONTENT)
            self.end_headers()
            return
        if req_path == "/":
            self.send_response(HTTPStatus.MOVED_PERMANENTLY)
            self.send_header("Location", SITE_ROOT)
            self.end_headers()
            return
        if req_path.startswith(LEGACY_SITE_ROOT):
            suffix = req_path[len(LEGACY_SITE_ROOT) :]
            location = f"{SITE_ROOT}{suffix}"
            if parsed.query:
                location = f"{location}?{parsed.query}"
            self.send_response(HTTPStatus.MOVED_PERMANENTLY)
            self.send_header("Location", location)
            self.end_headers()
            return
        super().do_GET()

    def translate_path(self, path: str) -> str:
        parsed = urlparse(path)
        req_path = unquote(parsed.path)

        if (
            req_path.startswith(f"{SITE_ROOT}docs/")
            or req_path.startswith(f"{LEGACY_SITE_ROOT}docs/")
            or req_path.startswith("/docs/")
        ):
            rel = req_path.split("/docs/", 1)[1]
            site_docs = os.path.join(BOOK_SITE, "docs", rel)
            if os.path.exists(site_docs):
                return site_docs
            return os.path.join(DOCS_SITE, rel)

        for root in (SITE_ROOT, LEGACY_SITE_ROOT):
            if req_path.startswith(root):
                rel = req_path[len(root) :]
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
        print(f"(legacy alias) http://localhost:{args.port}{LEGACY_SITE_ROOT}")
        print(f"{SITE_ROOT} -> {BOOK_SITE}")
        print(f"{SITE_ROOT}docs/ -> {os.path.join(BOOK_SITE, 'docs')} (fallback: {DOCS_SITE})")
        httpd.serve_forever()


if __name__ == "__main__":
    main()
