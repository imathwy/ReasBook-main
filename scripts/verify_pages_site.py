#!/usr/bin/env python3
"""Fail the Pages build if a catalogued project has no usable content."""

from __future__ import annotations

import json
import os
import sys
from pathlib import Path

from reasbook_catalog import NO_VERSO_PROJECTS


def main() -> None:
    projects = json.loads(os.environ["PROJECTS_JSON"])
    site_root = Path(".site")
    errors: list[str] = []

    for project in projects:
        slug = project["slug"]
        kind_title = project["kindTitle"]
        name = project["name"]

        docs_dir = site_root / "sites" / slug / "docs"
        pages_index = site_root / "sites" / slug / "pages" / "index.html"

        leaf = "Book.html" if kind_title == "Books" else "Paper.html"
        has_docs = (docs_dir / leaf).is_file()

        if name in NO_VERSO_PROJECTS:
            if not has_docs:
                errors.append(f"{name}: docs={leaf}={has_docs}")
        elif not pages_index.is_file():
            errors.append(f"{name}: missing sites/{slug}/pages/index.html")

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
        + f"{len(projects)} projects, "
        + f"{sum(1 for p in projects if (site_root / 'sites' / p['slug'] / 'pages' / 'index.html').is_file())} with pages"
    )


if __name__ == "__main__":
    main()
