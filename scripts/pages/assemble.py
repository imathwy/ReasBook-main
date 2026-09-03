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

import html
import json
import os
import re
import shutil
from pathlib import Path


ASSETS_DIR = Path(__file__).resolve().parent / "assets"


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


def has_index(path: Path) -> bool:
    return (path / "index.html").is_file()


def display_name(identifier: str) -> str:
    """Turn a repository identifier into a readable, stable catalog label."""

    if identifier == "TR_LALM_theory":
        return "TR-LALM Theory"

    def humanize(value: str) -> str:
        words = value.replace("_", " ")
        words = re.sub(r"(?<=[a-z0-9])(?=[A-Z])", " ", words)
        words = re.sub(r"(?<=[A-Za-z])(?=[0-9])", " ", words)
        words = re.sub(r"\s+", " ", words).strip()
        return words.replace("Introductionto ", "Introduction to ")

    parts = identifier.rsplit("_", 2)
    if len(parts) == 3 and re.fullmatch(r"(?:19|20)\d{2}", parts[2]):
        title, author, year = humanize(parts[0]), humanize(parts[1]), parts[2]
        return f"{title} ({author}, {year})"
    return humanize(identifier) or identifier


def page_head(title: str, stylesheet: str) -> list[str]:
    escaped_title = html.escape(title)
    return [
        "<head>",
        '  <meta charset="utf-8" />',
        '  <meta name="viewport" content="width=device-width,initial-scale=1" />',
        '  <meta name="theme-color" content="#17211c" />',
        f"  <title>{escaped_title}</title>",
        f'  <link rel="stylesheet" href="{html.escape(stylesheet, quote=True)}" />',
        "</head>",
    ]


def masthead(home_href: str, versions_href: str | None = None) -> list[str]:
    version_link = (
        f'<a class="masthead-link" href="{html.escape(versions_href, quote=True)}">'
        "Version Archive</a>"
        if versions_href
        else ""
    )
    return [
        '<a class="skip-link" href="#main-content">Skip to content</a>',
        '<header class="masthead">',
        '  <div class="masthead-inner">',
        f'    <a class="brand" href="{html.escape(home_href, quote=True)}">',
        '      <span class="proof-mark" aria-hidden="true">&#8866;</span>',
        "      <span><strong>ReasBook</strong><small>Formal Mathematics Library</small></span>",
        "    </a>",
        f"    {version_link}",
        "  </div>",
        "</header>",
    ]


def build_pages_tree(candidates: list[Path], dst: Path) -> None:
    """Copy the richest Verso tree, then guarantee ``dst/index.html``.

    The branch artifacts split a project's Verso landing page (often at
    ``<kind>/<slug>/index.html``) from its chapter/section routes (often at
    ``<slug>/...``).  ``best_dir`` alone can therefore produce a ``pages/``
    tree with content but no directory index, which GitHub Pages serves as a
    404.  Copy the richest tree first, overlay a landing index from any other
    candidate, and finally generate a minimal index for trees that never had
    one (for example the v4.26 aggregate library chapter trees).
    """
    present = [candidate for candidate in candidates if candidate.is_dir()]
    if not present:
        return

    content_src = best_dir(present)
    assert content_src is not None
    shutil.copytree(content_src, dst)

    if not has_index(dst):
        for candidate in present:
            if candidate != content_src and has_index(candidate):
                shutil.copy2(candidate / "index.html", dst / "index.html")
                break

    if not has_index(dst):
        write_pages_index(dst)


def write_pages_index(pages_dir: Path) -> None:
    """Generate a minimal landing page for a tree without a Verso index."""
    entries: list[tuple[str, str]] = []
    for child in sorted(pages_dir.iterdir()):
        if child.is_dir() and count_html(child) > 0:
            entries.append((f"./{child.name}/", child.name))

    (pages_dir / "index.html").write_text(
        html_page(
            "Pages",
            entries,
            "../",
            stylesheet="../../../static/catalog.css",
            home_href="../../../",
            eyebrow="Reading Index",
        ),
        encoding="utf-8",
    )


def write_docs_index(
    docs_dir: Path,
    leaf: str,
    *,
    stylesheet: str = "../../../static/catalog.css",
) -> None:
    """Add an index to a copied docs tree so ``./docs/`` is not a 404.

    The canonical docs tree contains ``Book.html``/``Paper.html`` plus module
    pages but has no directory index.  GitHub Pages does not render directory
    listings, so the site's ``Documentation`` nav link would otherwise 404 for
    every project.
    """
    (docs_dir / "index.html").write_text(
        "\n".join(
            [
                "<!doctype html>",
                '<html lang="en">',
                "<head>",
                '  <meta charset="utf-8" />',
                '  <meta name="viewport" content="width=device-width,initial-scale=1" />',
                f'  <meta http-equiv="refresh" content="0; url=./{leaf}" />',
                "  <title>Documentation</title>",
                f'  <link rel="stylesheet" href="{html.escape(stylesheet, quote=True)}" />',
                "</head>",
                '<body class="redirect-page">',
                f'  <p><a href="./{leaf}">Open Documentation</a></p>',
                "</body>",
                "</html>",
                "",
            ]
        ),
        encoding="utf-8",
    )


def write_redirect(path: Path, target: str, title: str) -> None:
    """Write a small, accessible redirect page to a preserved generated tree."""

    escaped_target = html.escape(target, quote=True)
    escaped_title = html.escape(title)
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(
        "\n".join(
            [
                "<!doctype html>",
                '<html lang="en">',
                "<head>",
                '  <meta charset="utf-8" />',
                '  <meta name="viewport" content="width=device-width,initial-scale=1" />',
                f'  <meta http-equiv="refresh" content="0; url={escaped_target}" />',
                f"  <title>{escaped_title}</title>",
                "</head>",
                "<body>",
                f'  <p><a href="{escaped_target}">{escaped_title}</a></p>',
                "</body>",
                "</html>",
                "",
            ]
        ),
        encoding="utf-8",
    )


def versioned_doc_entry(
    src_root: Path,
    project: dict[str, object],
) -> Path | None:
    """Find one project entry inside its untouched versioned doc-gen tree."""

    branch = str(project.get("branch", "")).strip()
    if not branch:
        return None
    kind = str(project["kind"])
    kind_title = str(project["kindTitle"])
    name = str(project["name"])
    leaf = "Book.html" if kind == "books" else "Paper.html"
    roots = (
        src_root / "versions" / branch / "docs" / "ReasBook",
        src_root / "versions" / branch / "docs",
    )
    for root in roots:
        for candidate in (
            root / kind_title / name / leaf,
            root / name / leaf,
            root / f"{name}.html",
        ):
            if candidate.is_file():
                return candidate
    return None


def html_page(
    title: str,
    links: list[tuple[str, str]],
    back_href: str,
    *,
    stylesheet: str,
    home_href: str,
    eyebrow: str = "Library Index",
) -> str:
    escaped_title = html.escape(title)
    items = "\n".join(
        "\n".join(
            [
                "      <li>",
                f'        <a class="resource-link" href="{html.escape(href, quote=True)}">',
                f"          <span>{html.escape(label)}</span>",
                '          <span class="link-arrow" aria-hidden="true">&#8594;</span>',
                "        </a>",
                "      </li>",
            ]
        )
        for href, label in links
    )
    if not items:
        items = '      <li class="empty-state">No published resources yet.</li>'
    return "\n".join(
        [
            "<!doctype html>",
            '<html lang="en">',
            *page_head(title, stylesheet),
            "<body>",
            *masthead(home_href),
            '  <main id="main-content" class="page-shell narrow-shell">',
            '    <section class="page-heading">',
            f'      <p class="eyebrow">{html.escape(eyebrow)}</p>',
            f"      <h1>{escaped_title}</h1>",
            "    </section>",
            '    <ul class="resource-list" role="list">',
            items,
            "    </ul>",
            f'    <a class="back-link" href="{html.escape(back_href, quote=True)}">'
            '<span aria-hidden="true">&#8592;</span> Back to ReasBook</a>',
            "  </main>",
            "</body>",
            "</html>",
            "",
        ]
    )


def project_page(
    project: dict[str, str],
    links: list[tuple[str, str]],
    *,
    has_versions: bool,
) -> str:
    name = project["name"]
    kind = project["kindTitle"].rstrip("s")
    branch = project.get("branch", "")
    title = display_name(name)
    items = "\n".join(
        "\n".join(
            [
                "      <li>",
                f'        <a class="resource-link" href="{html.escape(href, quote=True)}">',
                f"          <span>{html.escape(label)}</span>",
                '          <span class="link-arrow" aria-hidden="true">&#8594;</span>',
                "        </a>",
                "      </li>",
            ]
        )
        for href, label in links
    )
    if not items:
        items = '      <li class="empty-state">No published resources yet.</li>'
    return "\n".join(
        [
            "<!doctype html>",
            '<html lang="en">',
            *page_head(title, "../../static/catalog.css"),
            "<body>",
            *masthead("../../", "../../versions/" if has_versions else None),
            '  <main id="main-content" class="page-shell narrow-shell">',
            '    <nav class="breadcrumb" aria-label="Breadcrumb">',
            '      <a href="../../">ReasBook</a><span aria-hidden="true">/</span>',
            f"      <span>{html.escape(project['kindTitle'])}</span>",
            "    </nav>",
            '    <section class="page-heading project-heading">',
            f'      <p class="eyebrow">{html.escape(kind)} &middot; '
            f'<span translate="no">{html.escape(branch)}</span></p>',
            f"      <h1>{html.escape(title)}</h1>",
            f'      <code class="identifier" translate="no">{html.escape(name)}</code>',
            "    </section>",
            '    <ul class="resource-list" role="list">',
            items,
            "    </ul>",
            '    <a class="back-link" href="../../"><span aria-hidden="true">&#8592;</span> '
            "Back to ReasBook</a>",
            "  </main>",
            "</body>",
            "</html>",
            "",
        ]
    )


def catalog_page(projects: list[dict[str, str]], *, has_versions: bool) -> str:
    groups: list[str] = []
    for kind, heading in (("books", "Books"), ("papers", "Papers")):
        rows = sorted(
            (project for project in projects if project["kind"] == kind),
            key=lambda project: project["name"].lower(),
        )
        if not rows:
            continue
        links = []
        for project in rows:
            name = project["name"]
            links.extend(
                [
                    "      <li>",
                    f'        <a class="catalog-row" href="./sites/{html.escape(project["slug"], quote=True)}/">',
                    '          <span class="catalog-title">',
                    f"            <strong>{html.escape(display_name(name))}</strong>",
                    f'            <code translate="no">{html.escape(name)}</code>',
                    "          </span>",
                    '          <span class="catalog-version" translate="no">'
                    f"{html.escape(project.get('branch', ''))}</span>",
                    '          <span class="link-arrow" aria-hidden="true">&#8594;</span>',
                    "        </a>",
                    "      </li>",
                ]
            )
        groups.extend(
            [
                '    <section class="catalog-group">',
                '      <div class="group-heading">',
                f"        <h2>{heading}</h2>",
                f'        <span class="group-count">{len(rows)}</span>',
                "      </div>",
                '      <ul class="catalog-list" role="list">',
                *links,
                "      </ul>",
                "    </section>",
            ]
        )
    if not groups:
        groups = [
            '    <p class="empty-state">No published books or papers yet.</p>'
        ]
    versions_href = "./versions/" if has_versions else None
    return "\n".join(
        [
            "<!doctype html>",
            '<html lang="en">',
            *page_head("ReasBook", "./static/catalog.css"),
            "<body>",
            *masthead("./", versions_href),
            '  <main id="main-content" class="page-shell">',
            '    <section class="catalog-intro">',
            '      <p class="eyebrow">Lean Library Index</p>',
            "      <h1>ReasBook</h1>",
            "      <p>Books and papers formalized in Lean.</p>",
            "    </section>",
            *groups,
            "  </main>",
            '  <footer class="site-footer"><span>ReasBook</span><span>Formal Mathematics</span></footer>',
            "</body>",
            "</html>",
            "",
        ]
    )


def write_catalog_asset(dst_root: Path) -> None:
    source = ASSETS_DIR / "catalog.css"
    if not source.is_file():
        raise FileNotFoundError(f"missing catalog stylesheet: {source}")
    static = dst_root / "static"
    static.mkdir(parents=True, exist_ok=True)
    shutil.copy2(source, static / "catalog.css")


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
    write_catalog_asset(dst_root)
    has_versions = (dst_root / "versions" / "index.html").is_file()

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

    book_links: list[tuple[str, str]] = []
    paper_links: list[tuple[str, str]] = []

    for project in projects:
        slug = project["slug"]
        kind = project["kind"]
        kind_title = project["kindTitle"]
        name = project["name"]
        leaf = "Book.html" if kind == "books" else "Paper.html"

        docs_candidates = [
            src_root / "docs" / "ReasBook" / kind_title / name,
            src_root / "docs" / "ReasBook" / name,
            src_root / "docs" / kind_title / name,
            src_root / "docs" / name,
        ]
        docs_src = best_dir(docs_candidates)
        docs_file_candidates = (
            src_root / "docs" / "ReasBook" / kind_title / name / leaf,
            src_root / "docs" / "ReasBook" / name / leaf,
            src_root / "docs" / kind_title / name / leaf,
            src_root / "docs" / name / leaf,
            src_root / "docs" / "ReasBook" / f"{name}.html",
            src_root / "docs" / f"{name}.html",
        )
        docs_file = next(
            (candidate for candidate in docs_file_candidates if candidate.is_file()),
            None,
        )
        canonical_docs = docs_reasbook / kind_title / name
        preserved_doc = versioned_doc_entry(src_root, project)
        if preserved_doc is not None:
            published_doc = dst_root / preserved_doc.relative_to(src_root)
            relative_target = Path(
                os.path.relpath(published_doc, canonical_docs)
            ).as_posix()
            write_redirect(
                canonical_docs / leaf,
                relative_target,
                f"Open {display_name(name)} Documentation",
            )
        elif docs_src is not None:
            shutil.copytree(docs_src, canonical_docs)
            canonical_leaf = canonical_docs / leaf
            if not canonical_leaf.is_file():
                root_page_candidates = [
                    src_root / "docs" / "ReasBook" / f"{name}.html",
                    src_root / "docs" / f"{name}.html",
                ]
                root_page = next(
                    (
                        candidate
                        for candidate in root_page_candidates
                        if candidate.is_file()
                    ),
                    None,
                )
                if root_page is not None:
                    shutil.copy2(root_page, canonical_leaf)
        elif docs_file is not None:
            # Explicit Lake ``roots`` projects can emit only a root HTML file
            # (for example ``docs/ReasBook/TR_LALM_theory.html``) rather than
            # a directory named after the project. Normalize that file into
            # the canonical kind/project/leaf layout.
            canonical_docs.mkdir(parents=True, exist_ok=True)
            shutil.copy2(docs_file, canonical_docs / leaf)

        if canonical_docs.is_dir() and (canonical_docs / leaf).is_file():
            write_docs_index(
                canonical_docs,
                leaf,
                stylesheet="../../../../static/catalog.css",
            )

        pages_candidates = [
            src_root / kind / slug,
            src_root / slug,
        ]

        site_dir = sites_root / slug
        site_dir.mkdir(parents=True, exist_ok=True)

        site_nav: list[tuple[str, str]] = []
        if any(candidate.is_dir() for candidate in pages_candidates):
            build_pages_tree(pages_candidates, site_dir / "pages")
            site_nav.append(("./pages/", "Pages"))
        if canonical_docs.is_dir():
            site_docs = site_dir / "docs"
            site_docs.mkdir()
            canonical_target = Path(
                os.path.relpath(canonical_docs / leaf, site_docs)
            ).as_posix()
            write_redirect(
                site_docs / leaf,
                canonical_target,
                f"Open {display_name(name)} Documentation",
            )
            write_docs_index(
                site_docs,
                leaf,
                stylesheet="../../../static/catalog.css",
            )
            site_nav.append(("./docs/", "Documentation"))

        map_dir = dst_root / "theorem-maps" / kind / slug
        if map_dir.is_dir():
            site_nav.append(
                (f"../../theorem-maps/{kind}/{slug}/", "Theorem Map")
            )

        project_page_data = {str(key): str(value) for key, value in project.items()}
        (site_dir / "index.html").write_text(
            project_page(
                project_page_data,
                site_nav,
                has_versions=has_versions,
            ),
            encoding="utf-8",
        )

        if canonical_docs.is_dir():
            if kind == "books":
                book_links.append((f"./Books/{name}/", name))
            else:
                paper_links.append((f"./Papers/{name}/", name))

    # Documentation index pages point at the canonical ReasBook/<Kind>/ tree.
    (docs_reasbook / "index.html").write_text(
        "\n".join(
            [
                "<!doctype html>",
                '<html lang="en">',
                *page_head("ReasBook Documentation", "../../static/catalog.css"),
                "<body>",
                *masthead("../../", "../../versions/" if has_versions else None),
                '  <main id="main-content" class="page-shell narrow-shell">',
                '    <section class="page-heading">',
                '      <p class="eyebrow">API Reference</p>',
                "      <h1>Documentation</h1>",
                "    </section>",
                "    <h2>Books</h2>",
                '    <ul class="resource-list" role="list">',
                *[
                    f'      <li><a class="resource-link" href="{html.escape(href, quote=True)}"><span>{html.escape(display_name(label))}</span><span class="link-arrow" aria-hidden="true">&#8594;</span></a></li>'
                    for href, label in sorted(book_links)
                ],
                "    </ul>",
                "    <h2>Papers</h2>",
                '    <ul class="resource-list" role="list">',
                *[
                    f'      <li><a class="resource-link" href="{html.escape(href, quote=True)}"><span>{html.escape(display_name(label))}</span><span class="link-arrow" aria-hidden="true">&#8594;</span></a></li>'
                    for href, label in sorted(paper_links)
                ],
                "  </main>",
                "</body>",
                "</html>",
                "",
            ]
        ),
        encoding="utf-8",
    )
    (docs_root / "index.html").write_text(
        html_page(
            "Documentation",
            [("./ReasBook/", "Browse API Documentation")],
            "../",
            stylesheet="../static/catalog.css",
            home_href="../",
            eyebrow="Reference",
        ),
        encoding="utf-8",
    )

    # Root site index is the project catalog, regardless of whether a Verso
    # branch previously produced a root index.html.
    (dst_root / "index.html").write_text(
        catalog_page(projects, has_versions=has_versions),
        encoding="utf-8",
    )


if __name__ == "__main__":
    main()
