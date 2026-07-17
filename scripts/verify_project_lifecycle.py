#!/usr/bin/env python3
"""Validate project lifecycle evidence and its root-allowlist relationship."""

from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path

SCRIPT_DIR = Path(__file__).resolve().parent
sys.path.insert(0, str(SCRIPT_DIR))
from lib.project_lifecycle import validate_lifecycle
from lib.project_scope import discover

ROOT = SCRIPT_DIR.parent
PROJECT = ROOT / "ReasBook"


def inspect_manifest(payload: dict, *, allow_partial: bool = False) -> list[str]:
    findings: list[str] = []
    if payload.get("schema_version") != 1:
        findings.append("project lifecycle schema_version must be 1")
    migration_status = payload.get("migration_status")
    if migration_status not in {"in-progress", "complete"}:
        findings.append("project lifecycle migration_status must be in-progress or complete")
    records = payload.get("projects")
    if not isinstance(records, list):
        return findings + ["project lifecycle projects must be an array"]

    canonical = {spec.key: spec for spec in discover(PROJECT)}
    seen: set[str] = set()
    for index, record in enumerate(records):
        if not isinstance(record, dict):
            findings.append(f"projects[{index}] must be an object")
            continue
        key = record.get("project")
        if key in seen:
            findings.append(f"duplicate lifecycle project: {key}")
        seen.add(key)
        if key not in canonical:
            findings.append(f"unknown lifecycle project: {key}")
        if not record.get("run_id"):
            findings.append(f"{key or f'projects[{index}]'} is missing run_id")
        findings.extend(f"{key or f'projects[{index}]'}: {item}" for item in validate_lifecycle(record))

    if migration_status == "complete" or not allow_partial:
        missing = sorted(set(canonical) - seen)
        if missing:
            findings.append("lifecycle manifest is missing: " + ", ".join(missing))
    return findings


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--manifest", type=Path, required=True)
    parser.add_argument("--allow-partial", action="store_true")
    args = parser.parse_args()
    try:
        payload = json.loads(args.manifest.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError) as error:
        print(f"could not read lifecycle manifest: {error}", file=sys.stderr)
        return 2
    findings = inspect_manifest(payload, allow_partial=args.allow_partial)
    if findings:
        print("\n".join(findings), file=sys.stderr)
        return 1
    print(f"PASS project lifecycle: {len(payload['projects'])} project records")
    return 0


if __name__ == "__main__":
    sys.exit(main())
