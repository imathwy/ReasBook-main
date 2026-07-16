#!/usr/bin/env python3
"""Approve a verified compatibility tip and optional mechanical migration."""

from __future__ import annotations

import argparse
import json
import os
import re
import sys
from pathlib import Path

ROOT = Path(os.environ.get("REASBOOK_ROOT", Path(__file__).resolve().parents[1])).resolve()
REQUIRED_TRUE = (
    "reproducible_diagnostic", "module_build_pass",
    "downstream_checkpoint_pass", "no_proof_bypass",
)
REQUIRED_TEXT = (
    "id", "title", "diagnostic", "preconditions", "unsafe_cases",
    "repair_pattern", "verification", "provenance",
)
VALID_STATUS = {"confirmed", "conditional", "obsolete"}
VALID_LEVEL = {"manual", "suggest-only", "safe-auto-fix"}


def current_toolchain() -> str:
    text = (ROOT / "ReasBook" / "lean-toolchain").read_text(encoding="utf-8").strip()
    return text.rsplit(":v", 1)[-1]


def tip_block(data: dict, version: str, status: str, level: str) -> str:
    return "\n".join([
        f"## {data['id']}: {data['title']}", "",
        f"- Status: {status}",
        f"- Scope: Lean v{version}",
        f"- Diagnostic: {data['diagnostic']}",
        f"- Preconditions: {data['preconditions']}",
        f"- Unsafe cases: {data['unsafe_cases']}",
        f"- Repair pattern: {data['repair_pattern']}",
        f"- Verification: {data['verification']}",
        f"- Automation level: {level}",
        f"- Provenance: {data['provenance']}",
    ])


def upsert_section(content: str, tip_id: str, block: str) -> tuple[str, str]:
    pattern = re.compile(
        rf"^##\s+{re.escape(tip_id)}:.*?(?=^##\s+|\Z)",
        re.MULTILINE | re.DOTALL,
    )
    match = pattern.search(content)
    canonical = block.rstrip() + "\n\n"
    if not match:
        return content.rstrip() + "\n\n" + canonical, "added"
    existing = match.group(0).rstrip() + "\n\n"
    if existing == canonical:
        return content, "unchanged"
    return content[:match.start()] + canonical + content[match.end():].lstrip("\n"), "updated"


def prepare_migration(data: dict, version: str) -> tuple[Path, dict, str]:
    required = ("old_identifier", "new_identifier", "migration_note")
    missing = [key for key in required if not data.get(key)]
    if missing:
        raise ValueError(f"migration promotion missing fields: {missing}")
    path = ROOT / "docs" / "compatibility" / f"migrations-v{version}.json"
    rules = json.loads(path.read_text(encoding="utf-8")) if path.exists() else {}
    rule = {
        "new": data["new_identifier"],
        "since": f"v{version}",
        "note": data["migration_note"],
        "provenance": data["id"],
    }
    state = "unchanged" if rules.get(data["old_identifier"]) == rule else (
        "updated" if data["old_identifier"] in rules else "added"
    )
    rules[data["old_identifier"]] = rule
    return path, rules, state


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("candidate", type=Path)
    args = parser.parse_args()
    try:
        data = json.loads(args.candidate.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError) as error:
        print(f"rejected: invalid candidate: {error}", file=sys.stderr)
        return 1
    missing = [key for key in REQUIRED_TEXT if not data.get(key)]
    failed = [key for key in REQUIRED_TRUE if data.get(key) is not True]
    if missing or failed:
        print(f"rejected: missing={missing}, failed_gates={failed}", file=sys.stderr)
        return 1
    version = current_toolchain()
    if data.get("toolchain") not in (version, f"v{version}"):
        print("rejected: candidate must explicitly match the current toolchain", file=sys.stderr)
        return 1
    tip_version = ".".join(version.removeprefix("v").split(".")[:2])
    if not re.fullmatch(rf"TIP-{re.escape(tip_version)}-[A-Za-z0-9._-]+", data["id"]):
        print("rejected: tip ID is not scoped to the current toolchain", file=sys.stderr)
        return 1
    level = data.get("automation_level", "suggest-only")
    status = data.get("status", "confirmed")
    if level not in VALID_LEVEL or status not in VALID_STATUS:
        print("rejected: invalid status or automation level", file=sys.stderr)
        return 1
    fixtures = sorted(set(data.get("verified_fixtures", [])))
    if data.get("context_sensitive"):
        level, status = "suggest-only", "conditional"
    if (level == "safe-auto-fix" or data.get("promote_to_migration")) and len(fixtures) < 2:
        print("rejected: mechanical promotion requires at least two distinct fixtures", file=sys.stderr)
        return 1
    if data.get("promote_to_migration") and (level != "safe-auto-fix" or status != "confirmed"):
        print("rejected: migration promotion requires confirmed safe-auto-fix", file=sys.stderr)
        return 1

    migration_update = None
    if data.get("promote_to_migration"):
        try:
            migration_update = prepare_migration(data, version)
        except (ValueError, OSError, json.JSONDecodeError) as error:
            print(f"rejected migration promotion: {error}", file=sys.stderr)
            return 1

    destination = ROOT / "docs" / "compatibility" / f"v{version}.md"
    if not destination.exists():
        print("rejected: current toolchain compatibility document is missing", file=sys.stderr)
        return 1
    content = destination.read_text(encoding="utf-8")
    updated, tip_state = upsert_section(content, data["id"], tip_block(data, version, status, level))
    destination.write_text(updated, encoding="utf-8")
    migration_state = None
    if migration_update:
        path, rules, migration_state = migration_update
        path.write_text(
            json.dumps(rules, indent=2, ensure_ascii=False, sort_keys=True) + "\n",
            encoding="utf-8",
        )
    print(f"tip={tip_state}" + (f" migration={migration_state}" if migration_state else ""))
    return 0


if __name__ == "__main__":
    sys.exit(main())
