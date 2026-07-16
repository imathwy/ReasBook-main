#!/usr/bin/env python3
"""Generate or verify the root imports against a local project evidence matrix."""

from __future__ import annotations

import argparse
import json
import re
from pathlib import Path
import sys

SCRIPT_DIR = Path(__file__).resolve().parent
sys.path.insert(0, str(SCRIPT_DIR))
from lib.project_scope import discover

ROOT = SCRIPT_DIR.parent
PROJECT = ROOT / "ReasBook"
ACTIVE_RE = re.compile(r"^import\s+(\S+)$")
PENDING_RE = re.compile(
    r"^-- repair-pending: (?P<key>(?:book|paper):[^;]+); "
    r"last-run=(?P<run>[^;]+); status=(?P<status>repair-incomplete|infrastructure-failure)$"
)
DISABLED_RE = re.compile(r"^-- import\s+(\S+)$")


def expected_lines(matrix: dict) -> list[str]:
    evidence = {item["project"]: item for item in matrix["projects"]}
    lines = ["-- Root module for ReasBook", "import Mathlib"]
    for spec in discover(PROJECT):
        item = evidence.get(spec.key)
        if item is None:
            raise ValueError(f"matrix is missing {spec.key}")
        if item["status"] == "full-pass":
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


def inspect(root_text: str, matrix: dict) -> list[str]:
    expected = expected_lines(matrix)
    actual = root_text.splitlines()
    return [] if actual == expected else [
        "ReasBook/ReasBook.lean does not exactly match the evidence matrix"
    ]


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
    findings = inspect(root_entry.read_text(encoding="utf-8"), matrix)
    if findings:
        print("\n".join(findings), file=sys.stderr)
        return 1
    active = sum(item["status"] == "full-pass" for item in matrix["projects"])
    print(f"PASS root allowlist: {active} active / {len(matrix['projects'])} canonical projects")
    return 0


if __name__ == "__main__":
    sys.exit(main())
