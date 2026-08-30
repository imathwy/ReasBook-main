#!/usr/bin/env python3
"""Fail the Pages build if a catalogued project has no usable content."""

from __future__ import annotations

import json
import os
import sys
from pathlib import Path


def count_html(path: Path) -> int:
    if not path.is_dir():
        return 0
    return sum(1 for _ in path.rglob("*.html"))


def main() -> None:
    projects = json.loads(os.environ["PROJECTS_JSON"])
    site_root = Path(".site")
    errors: list[str] = []

    for project in projects:
        slug = project["slug"]
        kind_title = project["kindTitle"]
        name = project["name"]

        pages_dir = site_root / "sites" / slug / "pages"
        docs_dir = site_root / "sites" / slug / "docs"
        page_count = count_html(pages_dir)

        leaf = "Book.html" if kind_title == "Books" else "Paper.html"
        has_docs = (docs_dir / leaf).is_file()

        if page_count < 2 and not has_docs:
            errors.append(
                f"{name}: pages={page_count}, docs={leaf}={has_docs}"
            )

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

    print(
        "::notice title=ReasBook pages verified::"
        + f"{len(projects)} projects, {sum(1 for p in projects if count_html(site_root / 'sites' / p['slug'] / 'pages') >= 2)} with pages"
    )


if __name__ == "__main__":
    main()
