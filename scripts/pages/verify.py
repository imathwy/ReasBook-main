#!/usr/bin/env python3
"""Fail the Pages build if a catalogued project has no usable content."""

from __future__ import annotations

import json
import os
import re
import sys
from html.parser import HTMLParser
from pathlib import Path
from urllib.parse import unquote, urljoin, urlsplit

from project_catalog import NO_VERSO_PROJECTS


class _ReferenceParser(HTMLParser):
    def __init__(self) -> None:
        super().__init__(convert_charrefs=True)
        self.base_href: str | None = None
        self.references: list[tuple[str, str]] = []

    def handle_starttag(
        self,
        tag: str,
        attrs: list[tuple[str, str | None]],
    ) -> None:
        values = dict(attrs)
        if tag == "base":
            if self.base_href is None and values.get("href"):
                self.base_href = values["href"]
            return
        if (
            tag == "meta"
            and (values.get("http-equiv") or "").lower() == "refresh"
            and values.get("content")
        ):
            match = re.match(
                r"^\s*\d+(?:\.\d+)?\s*;\s*url\s*=\s*(.*?)\s*$",
                values["content"],
                flags=re.IGNORECASE,
            )
            if match and match.group(1):
                self.references.append(
                    ("refresh", match.group(1).strip("\"'"))
                )
        for attribute in ("href", "src"):
            value = values.get(attribute)
            if value:
                self.references.append((attribute, value))


def _base_path() -> str:
    value = os.environ.get("REASBOOK_SITE_ROOT", "/ReasBook/").strip()
    if not value.startswith("/"):
        value = "/" + value
    return value.rstrip("/") + "/"


def _navigation_documents(site_root: Path) -> list[Path]:
    """Return bounded, user-facing navigation pages worth link checking."""

    documents = set(site_root.rglob("index.html"))
    for pattern in (
        "docs/ReasBook/Books/*/Book.html",
        "docs/ReasBook/Papers/*/Paper.html",
        "sites/*/docs/Book.html",
        "sites/*/docs/Paper.html",
        "**/navbar.html",
    ):
        documents.update(site_root.glob(pattern))
    return sorted(path for path in documents if path.is_file())


def _missing_internal_references(site_root: Path) -> list[str]:
    origin = "https://reasbook.invalid"
    base_path = _base_path()
    resolved_site_root = site_root.resolve()
    missing: list[str] = []
    for document in _navigation_documents(site_root):
        parser = _ReferenceParser()
        parser.feed(document.read_text(encoding="utf-8", errors="replace"))
        relative_document = document.relative_to(site_root).as_posix()
        document_url = origin + base_path + relative_document
        document_base = (
            urljoin(document_url, parser.base_href)
            if parser.base_href
            else document_url
        )
        for attribute, reference in parser.references:
            value = reference.strip()
            if not value or value.startswith(("#", "data:", "javascript:")):
                continue
            resolved = urlsplit(urljoin(document_base, value))
            if (
                resolved.scheme not in {"http", "https"}
                or resolved.netloc != "reasbook.invalid"
            ):
                continue
            path = unquote(resolved.path)
            if not path.startswith(base_path):
                missing.append(
                    f"{relative_document}: {attribute} escapes {base_path}: {value}"
                )
                continue
            relative = path[len(base_path) :].lstrip("/")
            candidate = (site_root / relative).resolve()
            if (
                candidate != resolved_site_root
                and resolved_site_root not in candidate.parents
            ):
                missing.append(
                    f"{relative_document}: {attribute} escapes site tree: {value}"
                )
                continue
            if path.endswith("/") or candidate.is_dir():
                candidate = candidate / "index.html"
            if not candidate.is_file():
                missing.append(
                    f"{relative_document}: {attribute} target is missing: {value}"
                )
    return missing


def usable_html(path: Path) -> bool:
    if path.is_symlink() or not path.is_file() or path.stat().st_size == 0:
        return False
    prefix = path.read_text(encoding="utf-8", errors="replace")[:8192].lower()
    return "<!doctype html" in prefix or "<html" in prefix


def main() -> None:
    projects = json.loads(os.environ["PROJECTS_JSON"])
    site_root = Path(".site")
    errors: list[str] = []
    require_docs = os.environ.get("REASBOOK_REQUIRE_DOCS", "1") == "1"
    require_maps = os.environ.get("REASBOOK_REQUIRE_THEOREM_MAPS", "0") == "1"

    for project in projects:
        slug = project["slug"]
        kind_title = project["kindTitle"]
        name = project["name"]

        docs_dir = site_root / "sites" / slug / "docs"
        pages_dir = site_root / "sites" / slug / "pages"
        pages_index = pages_dir / "index.html"

        leaf = "Book.html" if kind_title == "Books" else "Paper.html"
        docs_leaf = docs_dir / leaf
        canonical_leaf = (
            site_root / "docs" / "ReasBook" / kind_title / name / leaf
        )

        if require_docs and (
            not usable_html(docs_leaf) or not usable_html(canonical_leaf)
        ):
            errors.append(
                f"{name}: missing usable canonical/project docs ({leaf})"
            )
        if name in NO_VERSO_PROJECTS:
            pass
        elif not usable_html(pages_index):
            errors.append(f"{name}: missing sites/{slug}/pages/index.html")
        if require_maps:
            map_index = (
                site_root
                / "theorem-maps"
                / project["kind"]
                / slug
                / "index.html"
            )
            if not usable_html(map_index):
                errors.append(f"{name}: missing usable theorem map")

    if errors:
        print("::error title=Incomplete ReasBook project::" + " ; ".join(errors))
        sys.exit(1)

    # The canonical docs tree must not contain any pre-normalization roots.
    docs_reasbook = site_root / "docs" / "ReasBook"
    unexpected = sorted(
        path.name
        for path in docs_reasbook.iterdir()
        if path.name not in {"Books", "Papers", "index.html"}
    )
    if unexpected:
        print(
            "::error title=Unexpected docs roots::"
            + ", ".join(unexpected)
        )
        sys.exit(1)

    missing_references = _missing_internal_references(site_root)
    if missing_references:
        preview = " ; ".join(missing_references[:20])
        suffix = (
            f" ; and {len(missing_references) - 20} more"
            if len(missing_references) > 20
            else ""
        )
        print("::error title=Broken ReasBook links::" + preview + suffix)
        sys.exit(1)

    print(
        "::notice title=ReasBook pages verified::"
        + f"{len(projects)} projects, "
        + f"{sum(1 for p in projects if (site_root / 'sites' / p['slug'] / 'pages' / 'index.html').is_file())} with pages"
    )


if __name__ == "__main__":
    main()
