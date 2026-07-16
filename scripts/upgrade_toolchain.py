#!/usr/bin/env python3
"""Prepare a ReasBook Lean toolchain upgrade for validation in a PR."""

from __future__ import annotations

import argparse
import json
import subprocess
import sys
import urllib.request
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
PROJECT = ROOT / "ReasBook"
TOOLCHAIN = PROJECT / "lean-toolchain"
LAKEFILE = PROJECT / "lakefile.lean"
API = "https://api.github.com/repos/leanprover/lean4/releases?per_page=30"


def latest_stable() -> str | None:
    try:
        request = urllib.request.Request(API, headers={"Accept": "application/vnd.github+json"})
        with urllib.request.urlopen(request, timeout=30) as response:
            releases = json.load(response)
        for release in releases:
            tag = release.get("tag_name", "")
            if not release.get("draft") and not release.get("prerelease") and all(x not in tag for x in ("-rc", "-nightly", "-pre")):
                return tag.removeprefix("v")
    except Exception as error:
        print(f"failed to query Lean releases: {error}", file=sys.stderr)
    return None


def current() -> str:
    return TOOLCHAIN.read_text(encoding="utf-8").strip().rsplit(":v", 1)[-1]


def compatibility_template(version: str, previous: str) -> str:
    return f"""# Lean/mathlib v{version} compatibility notes

**Status**: Candidate — requires verification under v{version}
**Previous version**: v{previous}
**Mathlib revision candidate**: pending `lake update`

This file is intentionally new for this toolchain. Tips from earlier versions
are candidates only until reproduced and verified by the deterministic gates in
`scripts/update_compatibility_tips.py`.
"""


def update_version_pins(content: str, old: str, target: str) -> str:
    """Update ReasBook dependencies that follow the Lean release series."""
    return content.replace(f'@ "v{old}"', f'@ "v{target}"').replace(
        f'@ "verso-v{old}"', f'@ "verso-v{target}"'
    )


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    choice = parser.add_mutually_exclusive_group(required=True)
    choice.add_argument("--target", help="target version, with or without v")
    choice.add_argument("--latest", action="store_true")
    choice.add_argument("--latest-check", action="store_true")
    parser.add_argument("--dry-run", action="store_true")
    args = parser.parse_args()
    if args.latest_check:
        version = latest_stable()
        if not version:
            return 1
        print(version)
        return 0
    old = current()
    target = (latest_stable() if args.latest else args.target.removeprefix("v"))
    if not target:
        return 1
    if target == old:
        print(f"already at v{old}")
        return 0
    knowledge = ROOT / "docs" / "compatibility" / f"v{target}.md"
    migrations = ROOT / "docs" / "compatibility" / f"migrations-v{target}.json"
    if args.dry_run:
        print(f"would update ReasBook from v{old} to v{target}")
        print(f"would initialize {knowledge.relative_to(ROOT)}")
        print(f"would initialize {migrations.relative_to(ROOT)}")
        return 0
    TOOLCHAIN.write_text(f"leanprover/lean4:v{target}\n", encoding="utf-8")
    lakefile_content = LAKEFILE.read_text(encoding="utf-8")
    updated_lakefile = update_version_pins(lakefile_content, old, target)
    if updated_lakefile == lakefile_content:
        raise SystemExit(f"no v{old} dependency pins found in ReasBook/lakefile.lean")
    LAKEFILE.write_text(updated_lakefile, encoding="utf-8")
    if not knowledge.exists():
        knowledge.write_text(compatibility_template(target, old), encoding="utf-8")
    if not migrations.exists():
        migrations.write_text("{}\n", encoding="utf-8")
    subprocess.run(["lake", "update"], cwd=PROJECT, check=True)
    try:
        manifest = json.loads((PROJECT / "lake-manifest.json").read_text(encoding="utf-8"))
        revision = next(
            package.get("rev") or package.get("version")
            for package in manifest.get("packages", []) if package.get("name") == "mathlib"
        )
        knowledge.write_text(
            knowledge.read_text(encoding="utf-8").replace(
                "**Mathlib revision candidate**: pending `lake update`",
                f"**Mathlib revision candidate**: `{revision}`",
            ),
            encoding="utf-8",
        )
    except (OSError, json.JSONDecodeError, StopIteration):
        pass
    print(f"prepared v{target}; run scripts/run_automation.py --all before creating the PR")
    return 0


if __name__ == "__main__":
    sys.exit(main())
