"""Shared helpers for discovering the cross-version ReasBook catalog.

This module deliberately keeps the catalog logic in one place so the CI
discovery step, site assembly, verification, and README maintenance all use
the same project set and exclusions.
"""

from __future__ import annotations

import re
import subprocess
from pathlib import Path


# Lean sources in these projects are known-broken on their current version
# branch.  They remain in the repository/README as source-only entries but are
# intentionally excluded from CI pages/docs generation.
EXCLUDED_PROJECTS = {
    "ProbabilityTheory_Klenke_2020",
    "ComputationalMethodsInverseProblems_Vogel_2002",
}


def load_registry_branches(repo_root: Path | None = None) -> list[dict[str, str]]:
    """Parse config/toolchains.yml into (version, status) records.

    Only branches with status other than ``empty`` are returned.  ``empty``
    branches are receivers that do not yet expose a buildable project.
    """
    root = repo_root or Path.cwd()
    text = (root / "config" / "toolchains.yml").read_text(encoding="utf-8")

    records: list[dict[str, str]] = []
    current: dict[str, str] | None = None
    for line in text.splitlines():
        match = re.match(r"^\s*-\s*version:\s*(\S+)\s*$", line)
        if match:
            current = {"version": match.group(1), "status": "active"}
            records.append(current)
            continue
        status_match = re.match(r"^\s*status:\s*(\S+)\s*$", line)
        if status_match and current is not None:
            current["status"] = status_match.group(1)

    return [record for record in records if record.get("status", "active") != "empty"]


def existing_branches(branches: list[str], repo_root: Path | None = None) -> list[str]:
    """Keep only branches that exist as ``origin/<branch>`` refs."""
    root = repo_root or Path.cwd()
    existing: list[str] = []
    for branch in branches:
        result = subprocess.run(
            ["git", "rev-parse", "--verify", "--quiet", f"origin/{branch}"],
            cwd=root,
            check=False,
            capture_output=True,
            text=True,
        )
        if result.returncode == 0:
            existing.append(branch)
    return existing


def discover_projects(
    branches: list[str], repo_root: Path | None = None
) -> tuple[list[str], list[dict[str, str]]]:
    """Return (branches_with_projects, projects) from ``origin/<branch>`` trees."""
    root = repo_root or Path.cwd()
    projects: list[dict[str, str]] = []
    seen: dict[tuple[str, str], int] = {}
    branches_with_projects: set[str] = set()

    scan_specs = (
        ("ReasBook/Books", "books", "Books", "Book"),
        ("ReasBook/Papers", "papers", "Papers", "Paper"),
    )

    for branch in branches:
        for kind_dir, kind_slug, kind_title, leaf in scan_specs:
            result = subprocess.run(
                ["git", "ls-tree", "-r", "--name-only", f"origin/{branch}", kind_dir],
                cwd=root,
                check=False,
                capture_output=True,
                text=True,
            )
            if result.returncode != 0:
                continue

            for line in result.stdout.splitlines():
                parts = line.split("/")
                # Top-level project root only: ReasBook/<Kind>/<Project>/<Leaf>.lean
                if len(parts) != 4 or parts[3] != f"{leaf}.lean":
                    continue
                name = parts[2]
                if name in EXCLUDED_PROJECTS:
                    continue

                key = (kind_slug, name)
                entry = {
                    "kind": kind_slug,
                    "kindTitle": kind_title,
                    "name": name,
                    "slug": name.lower(),
                    "branch": branch,
                }
                if key in seen:
                    projects[seen[key]] = entry
                else:
                    seen[key] = len(projects)
                    projects.append(entry)
                branches_with_projects.add(branch)

    active_branches = [branch for branch in branches if branch in branches_with_projects]
    return active_branches, projects
