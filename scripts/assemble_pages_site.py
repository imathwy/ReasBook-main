#!/usr/bin/env python3
"""Build the final Pages tree from the merged version-branch site artifacts.

The branch artifacts use two historical layout conventions:

* v4.26 aggregate libraries publish Verso pages under ``books/<slug>/`` and
  ``papers/<slug>/``, and docs under ``docs/ReasBook/Books|Papers/<name>/``.
* v4.30+ per-project libraries publish Verso pages under ``<slug>/`` and docs
  under ``docs/ReasBook/<name>/``.  v4.32.2 historically published docs under
  ``docs/<name>/``.

This script normalizes all of those inputs into one canonical site:

* docs are always ``docs/ReasBook/Books|Papers/<name>/``
* each project gets a ``sites/<slug>/pages`` copy containing the richest
  available Verso tree, and ``sites/<slug>/docs`` containing its canonical docs
* other Verso assets/routes remain in place so absolute links inside copied
  pages continue to work
"""

from __future__ import annotations

import json
import os
import shutil
from pathlib import Path


def count_html(path: Path) -> int:
    if not path.is_dir():
        return 0
    return sum(1 for _ in path.rglob("*.html"))


def best_dir(candidates: list[Path]) -> Path | None:
    best: Path | None = None
    best_count = 0
    for candidate in candidates:
        count = count_html(candidate)
        if count > best_count:
            best = candidate
            best_count = count
    return best


def html_page(title: str, links: list[tuple[str, str]], back_href: str) -> str:
    items = "\n".join(
        f'    <li><a href="{href}">{label}</a></li>' for href, label in links
    )
    return "\n".join(
        [
            "<!doctype html>",
            '<html lang="en">',
            "<head>",
            '  <meta charset="utf-8" />',
            '  <meta name="viewport" content="width=device-width,initial-scale=1" />',
            f"  <title>{title}</title>",
            "</head>",
            "<body>",
            f"  <h1>{title}</h1>",
            "  <ul>",
            items,
            "  </ul>",
            f'  <p><a href="{back_href}">Back to root</a></p>',
            "</body>",
            "</html>",
            "",
        ]
    )


def main() -> None:
    projects = json.loads(os.environ["PROJECTS_JSON"])
    src_root = Path(".artifacts/monolith")
    dst_root = Path(".site")

    if dst_root.exists():
        shutil.rmtree(dst_root)
    if src_root.exists():
        shutil.copytree(src_root, dst_root)
    else:
        dst_root.mkdir(parents=True)

    # Rebuild the docs tree canonically instead of merging several layouts.
    docs_root = dst_root / "docs"
    if docs_root.exists():
        shutil.rmtree(docs_root)
    docs_reasbook = docs_root / "ReasBook"
    (docs_reasbook / "Books").mkdir(parents=True, exist_ok=True)
    (docs_reasbook / "Papers").mkdir(parents=True, exist_ok=True)

    sites_root = dst_root / "sites"
    if sites_root.exists():
        shutil.rmtree(sites_root)
    sites_root.mkdir(parents=True, exist_ok=True)

    site_links: list[tuple[str, str]] = []
    book_links: list[tuple[str, str]] = []
    paper_links: list[tuple[str, str]] = []

    for project in projects:
        slug = project["slug"]
        kind = project["kind"]
        kind_title = project["kindTitle"]
        name = project["name"]

        docs_candidates = [
            src_root / "docs" / "ReasBook" / kind_title / name,
            src_root / "docs" / "ReasBook" / name,
            src_root / "docs" / kind_title / name,
            src_root / "docs" / name,
        ]
        docs_src = best_dir(docs_candidates)
        canonical_docs = docs_reasbook / kind_title / name
        if docs_src is not None:
            shutil.copytree(docs_src, canonical_docs)

        pages_candidates = [
            src_root / kind / slug,
            src_root / slug,
        ]
        pages_src = best_dir(pages_candidates)

        site_dir = sites_root / slug
        site_dir.mkdir(parents=True, exist_ok=True)

        site_nav: list[tuple[str, str]] = []
        if pages_src is not None:
            shutil.copytree(pages_src, site_dir / "pages")
            site_nav.append(("./pages/", "Pages"))
        if canonical_docs.is_dir():
            shutil.copytree(canonical_docs, site_dir / "docs")
            site_nav.append(("./docs/", "Documentation"))

        map_dir = dst_root / "theorem-maps" / kind / slug
        if map_dir.is_dir():
            site_nav.append(
                (f"../../theorem-maps/{kind}/{slug}/", "Theorem map")
            )

        (site_dir / "index.html").write_text(
            html_page(name, site_nav, "../../"),
            encoding="utf-8",
        )

        site_links.append((f"./sites/{slug}/", name))
        if canonical_docs.is_dir():
            if kind == "books":
                book_links.append((f"./{name}/", name))
            else:
                paper_links.append((f"./{name}/", name))

    # Documentation index pages point at the canonical ReasBook/<Kind>/ tree.
    (docs_reasbook / "index.html").write_text(
        "\n".join(
            [
                "<!doctype html>",
                '<html lang="en">',
                "<head>",
                '  <meta charset="utf-8" />',
                '  <meta name="viewport" content="width=device-width,initial-scale=1" />',
                "  <title>ReasBook Documentation</title>",
                "</head>",
                "<body>",
                "  <h1>ReasBook Documentation</h1>",
                '  <h2><a href="./Books/">Books</a></h2>',
                "  <ul>",
                *[f'    <li><a href="{href}">{label}</a></li>' for href, label in sorted(book_links)],
                "  </ul>",
                '  <h2><a href="./Papers/">Papers</a></h2>',
                "  <ul>",
                *[f'    <li><a href="{href}">{label}</a></li>' for href, label in sorted(paper_links)],
                "  </ul>",
                "</body>",
                "</html>",
                "",
            ]
        ),
        encoding="utf-8",
    )
    (docs_root / "index.html").write_text(
        html_page("ReasBook Documentation", [("./ReasBook/", "ReasBook")], "../"),
        encoding="utf-8",
    )

    # Root site index is the project catalog, regardless of whether a Verso
    # branch previously produced a root index.html.
    (dst_root / "index.html").write_text(
        html_page("ReasBook", sorted(site_links), "./"),
        encoding="utf-8",
    )


if __name__ == "__main__":
    main()
