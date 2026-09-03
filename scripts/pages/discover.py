#!/usr/bin/env python3
"""Emit the GitHub Actions job outputs used by the Pages workflow.

The output lines are intentionally ``key=<json>`` so callers can append this
script's stdout to ``$GITHUB_OUTPUT``.
"""

from __future__ import annotations

import json
import os
from pathlib import Path

from project_catalog import (
    EXCLUDED_PROJECTS,
    discover_projects,
    existing_branches,
    load_registry_branches,
)


def csv_set(name: str) -> set[str]:
    raw = (os.environ.get(name) or "").strip()
    if not raw:
        return set()
    return {item.strip() for item in raw.split(",") if item.strip()}


def branch_is_selected(branch: str, only: set[str], skip: set[str]) -> bool:
    if only and branch not in only:
        return False
    if branch in skip:
        return False
    return True


def project_is_selected(name: str, only: set[str], skip: set[str]) -> bool:
    if only and name not in only:
        return False
    if name in skip:
        return False
    return True


def recommended_parallelism() -> tuple[int, int]:
    """Return (branch_workers, project_workers) derived from the runner.

    Branch workers are conservative because GitHub Actions self-hosted runners
    usually run one job at a time; the value becomes useful once extra runner
    workers are registered. Project workers are the real in-job parallelism
    used for per-project docs generation.
    """
    cpu = os.cpu_count() or 1
    branch_workers = max(1, min(3, cpu // 8))
    project_workers = max(1, min(16, cpu // 2))
    return branch_workers, project_workers


def env_parallelism(name: str, fallback: int) -> int:
    raw = (os.environ.get(name) or "").strip()
    if raw.isdigit() and int(raw) > 0:
        return int(raw)
    return fallback


def main() -> None:
    repo_root = Path.cwd()
    registry = load_registry_branches(repo_root)
    only_branches = csv_set("REASBOOK_ONLY_BRANCHES")
    skip_branches = csv_set("REASBOOK_SKIP_BRANCHES")
    branches = [
        branch
        for branch in existing_branches([record["version"] for record in registry], repo_root)
        if branch_is_selected(branch, only_branches, skip_branches)
    ]
    branches, projects = discover_projects(branches, repo_root)

    only_projects = csv_set("REASBOOK_ONLY_PROJECTS")
    skip_projects = csv_set("REASBOOK_SKIP_PROJECTS")
    projects = [
        project for project in projects if project_is_selected(project["name"], only_projects, skip_projects)
    ]
    # Recompute the branch matrix after project filtering so `only_projects` /
    # `skip_projects` do not leave empty branch jobs in the matrix.
    branches = [
        branch for branch in branches if any(project["branch"] == branch for project in projects)
    ]

    excluded_projects = sorted(EXCLUDED_PROJECTS | skip_projects)
    auto_branch_parallelism, auto_project_parallelism = recommended_parallelism()
    branch_parallelism = env_parallelism("REASBOOK_MAX_PARALLEL_BRANCHES", auto_branch_parallelism)
    project_parallelism = env_parallelism("REASBOOK_MAX_PARALLEL_PROJECTS", auto_project_parallelism)

    event_name = os.environ.get("GITHUB_EVENT_NAME", "")
    event_path = Path(os.environ.get("GITHUB_EVENT_PATH", "/dev/null"))
    if event_name == "push":
        full_deploy = True
    elif event_name == "workflow_dispatch":
        payload = json.loads(event_path.read_text(encoding="utf-8"))
        raw = str((payload.get("inputs") or {}).get("full_deploy", "true")).strip().lower()
        full_deploy = raw in {"1", "true", "yes", "on"}
    else:
        full_deploy = False

    print(f"version_branches={json.dumps(branches, separators=(',', ':'))}")
    print(f"version_branch_count={len(branches)}")
    print(f"projects={json.dumps(projects, separators=(',', ':'))}")
    print(f"full_deploy={'true' if full_deploy else 'false'}")
    print(f"excluded_projects_csv={','.join(excluded_projects)}")
    print(f"only_projects_csv={','.join(sorted(only_projects))}")
    print(f"max_parallel_branches={json.dumps(branch_parallelism)}")
    print(f"doc_parallelism={json.dumps(project_parallelism)}")


if __name__ == "__main__":
    main()
