#!/usr/bin/env python3
"""Regenerate complete active Book.lean/Paper.lean imports without source sync."""

from __future__ import annotations

import argparse
import sys
from pathlib import Path

SCRIPT_DIR = Path(__file__).resolve().parent
sys.path.insert(0, str(SCRIPT_DIR))
from lib.project_scope import clear_degradation, discover, generate_entry, resolve, source_files

ROOT = SCRIPT_DIR.parent
PROJECT = ROOT / "ReasBook"


def restore(kind: str, name: str, dry_run: bool = False) -> None:
    spec = resolve(PROJECT, kind, name)
    if not spec.entry.is_file():
        raise ValueError(f"entry point not found: {kind}:{name} ({spec.entry})")
    if dry_run:
        print(f"[DRY RUN] {spec.key}: would write {len(source_files(spec))} imports to {spec.entry}")
        return
    count = generate_entry(spec)
    cleared = clear_degradation(ROOT, kind, name)
    print(f"{kind}:{name}: restored {count} active imports; approval_cleared={cleared}")


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    scope = parser.add_mutually_exclusive_group(required=True)
    scope.add_argument("--book")
    scope.add_argument("--paper")
    scope.add_argument("--all", action="store_true")
    parser.add_argument("--dry-run", action="store_true")
    args = parser.parse_args()
    specs = (
        [resolve(PROJECT, "book", args.book)] if args.book else
        [resolve(PROJECT, "paper", args.paper)] if args.paper else
        discover(PROJECT)
    )
    try:
        for spec in specs:
            restore(spec.kind, spec.name, args.dry_run)
    except (OSError, ValueError) as error:
        print(f"restore failed: {error}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
