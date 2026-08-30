#!/usr/bin/env python3
"""Emit the GitHub Actions job outputs used by the Pages workflow.

The output lines are intentionally ``key=<json>`` so callers can append this
script's stdout to ``$GITHUB_OUTPUT``.
"""

from __future__ import annotations

import json
import os
from pathlib import Path

from reasbook_catalog import discover_projects, existing_branches, load_registry_branches


def main() -> None:
    repo_root = Path.cwd()
    branches = existing_branches(
        [record["version"] for record in load_registry_branches(repo_root)],
        repo_root,
    )
    branches, projects = discover_projects(branches, repo_root)

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


if __name__ == "__main__":
    main()
