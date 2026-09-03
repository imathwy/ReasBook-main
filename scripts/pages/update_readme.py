#!/usr/bin/env python3
"""Regenerate the main README ``Resources`` column from the project catalog.

This is a maintenance tool, not a CI runtime dependency.  It preserves the
manually curated title/source/contributor columns and only replaces the final
column of the Books and Papers tables.
"""

from __future__ import annotations

import re
from pathlib import Path

from project_catalog import (
    EXCLUDED_PROJECTS,
    NO_VERSO_PROJECTS,
    discover_projects,
    existing_branches,
    load_registry_branches,
)


SITE_BASE = "https://optpku.github.io/ReasBook"

def resource_cell(project: dict[str, str]) -> str:
    name = project["name"]
    slug = project["slug"]
    kind = project["kind"]

    if name in EXCLUDED_PROJECTS:
        return "Source only (CI excluded)"

    if kind == "books":
        docs_href = f"{SITE_BASE}/docs/ReasBook/Books/{name}/Book.html"
    else:
        docs_href = f"{SITE_BASE}/docs/ReasBook/Papers/{name}/Paper.html"

    pieces = [f"[Docs]({docs_href})"]
    if name not in NO_VERSO_PROJECTS:
        pieces.append(f"[Verso]({SITE_BASE}/sites/{slug}/pages/)")
    else:
        pieces.append("Verso: TBD")

    if name == "TR_LALM_theory":
        pieces.append(
            f"[Theorem map]({SITE_BASE}/theorem-maps/papers/tr_lalm_theory/)"
        )

    return "<br>".join(pieces)


def main() -> None:
    repo_root = Path.cwd()
    branches = existing_branches(
        [record["version"] for record in load_registry_branches(repo_root)],
        repo_root,
    )
    _, projects = discover_projects(branches, repo_root)
    by_key = {
        (project["kind"], project["name"]): project
        for project in projects
    }
    # Keep excluded source-only entries present in the table.
    for kind, name, kind_title in (
        ("books", "ProbabilityTheory_Klenke_2020", "Books"),
        ("books", "ComputationalMethodsInverseProblems_Vogel_2002", "Books"),
    ):
        by_key[(kind, name)] = {
            "kind": kind,
            "kindTitle": kind_title,
            "name": name,
            "slug": name.lower(),
            "branch": "",
        }

    readme = repo_root / "README.md"
    lines = readme.read_text(encoding="utf-8").splitlines()
    project_ref = re.compile(r"ReasBook/(Books|Papers)/([A-Za-z0-9_]+)/")

    changed = 0
    for index, line in enumerate(lines):
        if not line.startswith("| **["):
            continue
        match = project_ref.search(line)
        if not match:
            continue
        kind = "books" if match.group(1) == "Books" else "papers"
        name = match.group(2)
        project = by_key.get((kind, name))
        if project is None:
            continue

        cells = line.split("|")
        if len(cells) != 6:
            continue
        new_resources = f" {resource_cell(project)} "
        if cells[4] != new_resources:
            cells[4] = new_resources
            lines[index] = "|".join(cells)
            changed += 1

    if changed:
        readme.write_text("\n".join(lines) + "\n", encoding="utf-8")
        print(f"Updated {changed} resource cells")
    else:
        print("No resource cells changed")


if __name__ == "__main__":
    main()
