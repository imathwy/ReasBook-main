#!/usr/bin/env python3
"""Capture the read-only repository inventory required by baseline campaigns."""

from __future__ import annotations

import argparse
from collections import Counter
from datetime import datetime, timezone
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys

SCRIPT_DIR = Path(__file__).resolve().parent
sys.path.insert(0, str(SCRIPT_DIR))
from lib.project_scope import discover

ROOT = Path(os.environ.get("REASBOOK_ROOT", SCRIPT_DIR.parent)).resolve()
PROJECT = ROOT / "ReasBook"
REPORTS = ROOT / "docs" / "automation-reports"


def run(command: list[str], cwd: Path = ROOT) -> subprocess.CompletedProcess[str]:
    return subprocess.run(
        command, cwd=cwd, text=True, stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT, check=False,
    )


def git_output(*args: str) -> str:
    result = run(["git", *args])
    return result.stdout.strip() if result.returncode == 0 else f"ERROR: {result.stdout.strip()}"


def status_counts(lines: list[str]) -> dict[str, dict[str, int]]:
    counts: dict[str, Counter[str]] = {}
    for line in lines:
        if len(line) < 4:
            continue
        state = line[:2]
        path = line[3:].split(" -> ")[-1]
        top = path.split("/", 1)[0]
        counts.setdefault(top, Counter())[state] += 1
    return {top: dict(sorted(states.items())) for top, states in sorted(counts.items())}


def latest_run() -> str | None:
    version = (PROJECT / "lean-toolchain").read_text(encoding="utf-8").strip().rsplit(":v", 1)[-1]
    directory = REPORTS / f"v{version}"
    candidates = [path for path in directory.iterdir() if path.is_dir()] if directory.is_dir() else []
    return max(candidates, key=lambda path: path.stat().st_mtime).name if candidates else None


def project_inventory() -> list[dict[str, object]]:
    projects = []
    for spec in discover(PROJECT):
        source_count = sum(
            1 for path in spec.directory.rglob("*.lean")
            if ".lake" not in path.parts and path.name not in {"Book.lean", "Paper.lean"}
        )
        active_count = sum(
            1 for line in spec.entry.read_text(encoding="utf-8", errors="replace").splitlines()
            if line.lstrip().startswith("import ") and not line.lstrip().startswith("import Mathlib")
        )
        projects.append({
            "key": spec.key,
            "entry": str(spec.entry.relative_to(PROJECT)),
            "target": spec.target,
            "source_count": source_count,
            "active_import_count": active_count,
        })
    return projects


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--run-id")
    args = parser.parse_args()
    toolchain = (PROJECT / "lean-toolchain").read_text(encoding="utf-8").strip()
    version = toolchain.rsplit(":v", 1)[-1]
    short_head = git_output("rev-parse", "--short=8", "HEAD")
    run_id = args.run_id or f"{datetime.now(timezone.utc):%Y%m%dT%H%M%SZ}-baseline-inventory-{short_head}"
    previous_run = latest_run()
    out = REPORTS / f"v{version}" / run_id
    out.mkdir(parents=True, exist_ok=False)

    status = run(["git", "status", "--porcelain=v1", "--untracked-files=all"])
    status_lines = status.stdout.splitlines()
    (out / "git-status.txt").write_text(status.stdout, encoding="utf-8")
    changed = run(["git", "diff", "--name-status", "HEAD"])
    (out / "git-diff-name-status.txt").write_text(changed.stdout, encoding="utf-8")
    processes = run(["ps", "-eo", "pid,etime,cmd"])
    lean_processes = [
        line for line in processes.stdout.splitlines()
        if any(Path(token).name in {"lean", "lake"} for token in line.split())
    ]
    disk = shutil.disk_usage(ROOT)
    manifest = json.loads((PROJECT / "lake-manifest.json").read_text(encoding="utf-8"))
    mathlib = next(
        (package.get("rev") or package.get("version") for package in manifest.get("packages", [])
         if package.get("name") == "mathlib"),
        "unknown",
    )
    payload = {
        "run_id": run_id,
        "captured_at_utc": datetime.now(timezone.utc).isoformat(),
        "head": git_output("rev-parse", "HEAD"),
        "branch": git_output("branch", "--show-current"),
        "remotes": git_output("remote", "-v").splitlines(),
        "toolchain": toolchain,
        "mathlib_revision": mathlib,
        "status_exit_code": status.returncode,
        "status_line_count": len(status_lines),
        "status_counts_by_top_path": status_counts(status_lines),
        "lean_lake_processes": lean_processes,
        "disk_bytes": {"total": disk.total, "used": disk.used, "free": disk.free},
        "latest_automation_run_before_inventory": previous_run,
        "projects": project_inventory(),
        "known_unverified_files": [
            "ReasBook/Books/ConvexAnalysis_Rockafellar_1970/Chap02/Theorem_8_7.lean"
        ],
    }
    (out / "inventory.json").write_text(
        json.dumps(payload, indent=2, ensure_ascii=False) + "\n", encoding="utf-8"
    )
    summary = [
        f"# Baseline inventory {run_id}", "",
        f"- HEAD: `{payload['head']}`",
        f"- Branch: `{payload['branch']}`",
        f"- Toolchain: `{toolchain}`",
        f"- Mathlib revision: `{mathlib}`",
        f"- Worktree status records: `{len(status_lines)}`",
        f"- Canonical projects: `{len(payload['projects'])}`",
        f"- Lean/lake processes: `{len(lean_processes)}`",
        f"- Disk free bytes: `{disk.free}`", "",
        "See `inventory.json`, `git-status.txt`, and `git-diff-name-status.txt` for complete evidence.", "",
    ]
    (out / "summary.md").write_text("\n".join(summary), encoding="utf-8")
    print(f"run_id={run_id}\nreport={out.relative_to(ROOT)}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
