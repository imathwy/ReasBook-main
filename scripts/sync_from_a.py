#!/usr/bin/env python3
"""Sync per-statement files from ALLBOOKS (repo A) to this repository (repo B).

Copies files directly without reorganization — preserves the original
flat/Items/Roman numeral directory structure from ALLBOOKS.

Usage:
    python3 scripts/sync_from_a.py --source /tmp/repo-A --all
    python3 scripts/sync_from_a.py --source /tmp/repo-A --book RiemannSurfaces
    python3 scripts/sync_from_a.py --source /tmp/repo-A --all --dry-run
"""

import argparse
import shutil
import sys
from pathlib import Path

SCRIPT_DIR = Path(__file__).resolve().parent
REPO_ROOT = SCRIPT_DIR.parent
BOOKS_DIR = REPO_ROOT / "ReasBook" / "Books"

# ALLBOOKS dir → B dir mapping (where names differ)
DIR_MAP = {
    "JPMay": "MayConciseRevised",
    "AchimKlenke_runner": "AchimKlenkeLean",
    "Bauschke_runner": "BauschkeLean",
    "serre": "Serre",
    "stacks-refine-stmt": "stacks_project",
    "chapter1_reference_format_20260519_statement": "chapter1_reference_format",
}


def sync_book(source_repo: Path, dir_name: str, dry_run: bool):
    """Copy per-statement files from A to B."""
    src_dir = source_repo / dir_name
    if not src_dir.exists():
        print(f"  Source not found: {src_dir}")
        return

    # Map to B directory name
    b_name = DIR_MAP.get(dir_name, dir_name)
    dst_dir = BOOKS_DIR / b_name

    if dry_run:
        print(f"  [DRY RUN] {src_dir} → {dst_dir}")
        return

    if dst_dir.exists():
        shutil.rmtree(dst_dir)
    shutil.copytree(src_dir, dst_dir)
    count = len(list(dst_dir.rglob("*.lean")))
    print(f"  Synced: {dir_name} → {b_name} ({count} .lean files)")


def main():
    parser = argparse.ArgumentParser(description="Sync files from ALLBOOKS")
    parser.add_argument("--source", required=True, help="Path to ALLBOOKS clone")
    parser.add_argument("--all", action="store_true", help="Sync all books")
    parser.add_argument("--book", help="Sync a specific ALLBOOKS directory")
    parser.add_argument("--dry-run", action="store_true", help="Preview only")
    args = parser.parse_args()

    source = Path(args.source)
    if not source.exists():
        print(f"ERROR: Source not found: {source}", file=sys.stderr)
        sys.exit(1)

    if args.book:
        sync_book(source, args.book, args.dry_run)
    elif args.all:
        for d in sorted(source.iterdir()):
            if d.is_dir() and any(d.rglob("*.lean")):
                sync_book(source, d.name, args.dry_run)
    else:
        parser.print_help()


if __name__ == "__main__":
    main()
