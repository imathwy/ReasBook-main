#!/usr/bin/env python3
"""Generate or verify the root imports against a local project evidence matrix."""

from __future__ import annotations

import argparse
import json
import re
import subprocess
from pathlib import Path
import sys

SCRIPT_DIR = Path(__file__).resolve().parent
sys.path.insert(0, str(SCRIPT_DIR))
from lib.project_scope import discover
from lib.project_lifecycle import require_valid_lifecycle

ROOT = SCRIPT_DIR.parent
PROJECT = ROOT / "ReasBook"
ACTIVE_RE = re.compile(r"^import\s+(\S+)$")
PENDING_RE = re.compile(
    r"^-- repair-pending: (?P<key>(?:book|paper):[^;]+); "
    r"last-run=(?P<run>[^;]+); status=(?P<status>repair-incomplete|infrastructure-failure)$"
)
DISABLED_RE = re.compile(r"^-- import\s+(\S+)$")


def _evidence_items(payload: dict) -> list[dict]:
    """Normalize legacy run matrices and lifecycle manifests."""
    items = payload["projects"]
    if payload.get("schema_version") != 1:
        return items
    normalized = []
    for item in items:
        require_valid_lifecycle(item)
        normalized.append({
            "project": item["project"],
            "status": item["run_result"],
            "run_id": item["run_id"],
            "project_state": item["project_state"],
        })
    return normalized


def expected_lines(matrix: dict) -> list[str]:
    items = _evidence_items(matrix)
    evidence = {item["project"]: item for item in items}
    lines = ["-- Root module for ReasBook", "import Mathlib"]
    for spec in discover(PROJECT):
        item = evidence.get(spec.key)
        if item is None:
            raise ValueError(f"matrix is missing {spec.key}")
        active = item["status"] == "full-pass"
        if "project_state" in item:
            active = active and item["project_state"] == "full-pass"
        if active:
            lines.append(f"import {spec.target}")
        else:
            lines.extend([
                f"-- repair-pending: {spec.key}; last-run={item['run_id']}; status={item['status']}",
                f"-- import {spec.target}",
            ])
    unknown = sorted(set(evidence) - {spec.key for spec in discover(PROJECT)})
    if unknown:
        raise ValueError(f"matrix has unknown projects: {', '.join(unknown)}")
    return lines


def _recorded_commit(target_revision: str) -> str | None:
    match = re.fullmatch(r"(?:worktree@)?([0-9a-f]{40})(?::[0-9a-f]+)?", target_revision)
    return match.group(1) if match else None


def project_matches_revision(spec, target_revision: str, *, repo_root: Path = ROOT) -> bool:
    """Return whether one canonical project path still matches its validated commit."""
    commit = _recorded_commit(target_revision)
    if commit is None:
        return False
    relative = spec.directory.relative_to(repo_root)
    committed = subprocess.run(
        ["git", "diff", "--quiet", commit, "--", str(relative)],
        cwd=repo_root, check=False,
    )
    if committed.returncode != 0:
        return False
    untracked = subprocess.run(
        ["git", "ls-files", "--others", "--exclude-standard", "--", str(relative)],
        cwd=repo_root, text=True, stdout=subprocess.PIPE, stderr=subprocess.PIPE, check=False,
    )
    return untracked.returncode == 0 and not untracked.stdout.strip()


def inspect(root_text: str, matrix: dict, *, verify_fingerprints: bool = False) -> list[str]:
    expected = expected_lines(matrix)
    actual = root_text.splitlines()
    findings = [] if actual == expected else [
        "ReasBook/ReasBook.lean does not exactly match the evidence matrix"
    ]
    if verify_fingerprints:
        records = {item["project"]: item for item in matrix["projects"]}
        for spec in discover(PROJECT):
            record = records[spec.key]
            if record.get("run_result") != "full-pass" or record.get("project_state") != "full-pass":
                continue
            if not project_matches_revision(spec, str(record.get("target_revision", ""))):
                findings.append(
                    f"active project fingerprint is stale: {spec.key}; rerun canonical validation"
                )
    return findings


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--matrix", type=Path, required=True)
    parser.add_argument("--write", action="store_true")
    args = parser.parse_args()
    matrix = json.loads(args.matrix.read_text(encoding="utf-8"))
    root_entry = PROJECT / "ReasBook.lean"
    expected = "\n".join(expected_lines(matrix)) + "\n"
    if args.write:
        root_entry.write_text(expected, encoding="utf-8")
    findings = inspect(
        root_entry.read_text(encoding="utf-8"), matrix, verify_fingerprints=True,
    )
    if findings:
        print("\n".join(findings), file=sys.stderr)
        return 1
    items = _evidence_items(matrix)
    active = sum(
        item["status"] == "full-pass" and item.get("project_state", "full-pass") == "full-pass"
        for item in items
    )
    print(f"PASS root allowlist: {active} active / {len(items)} canonical projects")
    return 0


if __name__ == "__main__":
    sys.exit(main())
