#!/usr/bin/env python3
"""Validate tracked ALLBOOKS synchronization provenance records."""

from __future__ import annotations

import argparse
import json
import re
import sys
from pathlib import Path

SCRIPT_DIR = Path(__file__).resolve().parent
sys.path.insert(0, str(SCRIPT_DIR))
from sync_from_a import (
    DIR_MAP, PAPER_SOURCE_PROJECTS, normalization_profile, paper_normalization_profile,
)

HEX40 = re.compile(r"^[0-9a-f]{40}$")
HEX64 = re.compile(r"^[0-9a-f]{64}$")


def inspect(payload: dict) -> list[str]:
    findings: list[str] = []
    if payload.get("schema_version") != 1:
        findings.append("sync-state schema_version must be 1")
    source = payload.get("source")
    if not isinstance(source, dict) or source.get("name") != "ALLBOOKS" or not source.get("url"):
        findings.append("sync-state source must name ALLBOOKS and provide its URL")
    projects = payload.get("projects")
    if not isinstance(projects, dict):
        return findings + ["sync-state projects must be an object"]
    for key, entry in sorted(projects.items()):
        if not key.startswith(("book:", "paper:")) or not isinstance(entry, dict):
            findings.append(f"invalid sync-state project entry: {key}")
            continue
        source_directory = entry.get("source_directory")
        kind, name = key.split(":", 1)
        if kind == "book":
            expected_name = DIR_MAP.get(source_directory, source_directory)
            expected_profile = normalization_profile(source_directory)["id"]
        else:
            expected_name = PAPER_SOURCE_PROJECTS.get(source_directory)
            try:
                expected_profile = paper_normalization_profile(source_directory, name)["id"]
            except ValueError:
                expected_profile = None
        if name != expected_name:
            findings.append(f"{key}: source_directory does not map to the project key")
        if entry.get("normalization_profile") != expected_profile:
            findings.append(f"{key}: normalization profile is not current")
        if not HEX40.fullmatch(str(entry.get("accepted_upstream_commit", ""))):
            findings.append(f"{key}: accepted_upstream_commit must be a full SHA-1")
        if not HEX64.fullmatch(str(entry.get("normalized_tree_sha256", ""))):
            findings.append(f"{key}: normalized_tree_sha256 must be a SHA-256")
        for field in (
            "normalizer_commit", "accepted_in_reasbook_commit", "last_sync_report",
        ):
            if not entry.get(field):
                findings.append(f"{key}: missing {field}")
    return findings


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--state", type=Path, required=True)
    args = parser.parse_args()
    try:
        payload = json.loads(args.state.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError) as error:
        print(f"could not read sync state: {error}", file=sys.stderr)
        return 2
    findings = inspect(payload)
    if findings:
        print("\n".join(findings), file=sys.stderr)
        return 1
    print(f"PASS sync state: {len(payload['projects'])} project baseline(s)")
    return 0


if __name__ == "__main__":
    sys.exit(main())
