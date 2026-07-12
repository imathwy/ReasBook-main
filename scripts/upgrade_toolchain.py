#!/usr/bin/env python3
"""
Upgrade the Lean/mathlib toolchain for the ReasBook repository.

Usage:
    python3 scripts/upgrade_toolchain.py --latest --dry-run
    python3 scripts/upgrade_toolchain.py --latest
    python3 scripts/upgrade_toolchain.py --target v4.31.0
    python3 scripts/upgrade_toolchain.py --latest-check   # just print latest version
"""

import argparse
import json
import os
import re
import subprocess
import sys
import urllib.request
from collections import defaultdict
from datetime import datetime
from pathlib import Path

SCRIPT_DIR = Path(__file__).resolve().parent
REPO_ROOT = SCRIPT_DIR.parent

REASBOOK_TOOLCHAIN = REPO_ROOT / "ReasBook" / "lean-toolchain"
REASBOOKWEB_TOOLCHAIN = REPO_ROOT / "ReasBookWeb" / "lean-toolchain"
UPGRADE_REPORTS_DIR = REPO_ROOT / "docs" / "upgrade-reports"

GITHUB_API = "https://api.github.com/repos/leanprover/lean4/releases"


def get_latest_stable_lean() -> str | None:
    """Query GitHub API for the latest stable Lean 4 release."""
    try:
        req = urllib.request.Request(
            GITHUB_API + "?per_page=30",
            headers={"Accept": "application/vnd.github+json"},
        )
        with urllib.request.urlopen(req, timeout=30) as r:
            releases = json.load(r)

        for rel in releases:
            tag = rel.get("tag_name", "")
            if rel.get("prerelease") or rel.get("draft"):
                continue
            if any(skip in tag for skip in ("-rc", "-nightly", "-pre")):
                continue
            return tag.lstrip("v")
    except Exception as e:
        print(f"Error querying GitHub API: {e}", file=sys.stderr)
    return None


def get_current_version() -> str:
    """Read the current Lean version from the ReasBook lean-toolchain file."""
    content = REASBOOK_TOOLCHAIN.read_text().strip()
    return content.removeprefix("leanprover/lean4:v")


def create_tag(version: str):
    """Create and push a toolchain-v{version} tag."""
    tag = f"toolchain-v{version}"
    subprocess.run(["git", "tag", tag], cwd=REPO_ROOT, check=True)
    subprocess.run(["git", "push", "origin", tag], cwd=REPO_ROOT, check=True)
    print(f"Created and pushed tag: {tag}")


def update_toolchain_files(target_version: str):
    """Update lean-toolchain files to the new version."""
    content = f"leanprover/lean4:v{target_version}\n"
    REASBOOK_TOOLCHAIN.write_text(content)
    REASBOOKWEB_TOOLCHAIN.write_text(content)
    print(f"Updated toolchain to v{target_version}")


def update_dependencies():
    """Run lake update in ReasBook and ReasBookWeb."""
    for project in ["ReasBook", "ReasBookWeb"]:
        print(f"Running lake update in {project}/...")
        subprocess.run(["lake", "update"], cwd=REPO_ROOT / project, check=True)


def build_all() -> tuple[bool, str]:
    """Build the entire ReasBook project. Returns (success, stderr)."""
    result = subprocess.run(
        ["lake", "build"],
        cwd=REPO_ROOT / "ReasBook",
        capture_output=True,
        text=True,
    )
    return result.returncode == 0, result.stderr


def classify_errors(lake_output: str) -> dict[str, list[str]]:
    """Classify lake build errors by type. No auto-fix."""
    classified = defaultdict(list)

    for line in lake_output.split("\n"):
        line = line.strip()
        if not line or "error" not in line.lower():
            continue

        if "unknown identifier" in line:
            classified["unknown_identifier"].append(line)
        elif "unknown namespace" in line:
            classified["unknown_namespace"].append(line)
        elif "type mismatch" in line:
            classified["type_mismatch"].append(line)
        elif "universe" in line.lower() and "already declared" in line:
            classified["universe_conflict"].append(line)
        elif "imports itself" in line or "self" in line.lower():
            classified["circular_import"].append(line)
        elif "no such file" in line or "not found" in line.lower():
            classified["missing_module"].append(line)
        elif "unsolved goals" in line:
            classified["unsolved_goals"].append(line)
        else:
            classified["other"].append(line)

    return dict(classified)


def group_errors_by_book(classified: dict) -> dict[str, list[dict]]:
    """Group errors by affected book."""
    books = defaultdict(list)
    for error_type, errors in classified.items():
        for err in errors:
            # Try to extract book name from error line
            # Lake errors usually include file paths like Books/BookName/Chapters/...
            match = re.search(r"Books/([^/]+)/", err)
            book = match.group(1) if match else "unknown"
            books[book].append({"type": error_type, "message": err})
    return dict(books)


def list_affected_books(classified: dict) -> list[str]:
    """List books affected by errors."""
    books = set()
    for errors in classified.values():
        for err in errors:
            match = re.search(r"Books/([^/]+)/", err)
            if match:
                books.add(match.group(1))
    return sorted(books)


def generate_report(
    current: str,
    target: str,
    tag: str,
    success: bool,
    classified: dict,
    dry_run: bool,
):
    """Generate an upgrade report in docs/upgrade-reports/."""
    UPGRADE_REPORTS_DIR.mkdir(parents=True, exist_ok=True)
    report_path = UPGRADE_REPORTS_DIR / f"v{target}.md"

    books = group_errors_by_book(classified)
    affected = list_affected_books(classified)

    lines = [
        f"# Toolchain Upgrade Report: v{current} → v{target}",
        "",
        f"**Date**: {datetime.now().strftime('%Y-%m-%d %H:%M')}",
        f"**Tag**: `{tag}`",
        f"**Result**: {'PASS' if success else 'FAIL'}",
        f"**Mode**: {'DRY RUN' if dry_run else 'LIVE'}",
        "",
        "## Summary",
        "",
        f"- Build: {'passed' if success else 'failed'}",
        f"- Affected books: {len(affected)}",
        f"- Error categories: {len(classified)}",
        "",
    ]

    if not success:
        lines += [
            "## Books with errors",
            "",
        ]
        for book in affected:
            book_errors = books.get(book, [])
            lines.append(f"### {book} ({len(book_errors)} errors)")
            lines.append("")
            by_type = defaultdict(list)
            for e in book_errors:
                by_type[e["type"]].append(e["message"])
            for etype, msgs in sorted(by_type.items()):
                lines.append(f"- **{etype}**: {len(msgs)}")
                for m in msgs[:5]:
                    lines.append(f"  - `{m[:120]}`")
                if len(msgs) > 5:
                    lines.append(f"  - ... and {len(msgs) - 5} more")
            lines.append("")

        lines += [
            "## Error type summary",
            "",
        ]
        for etype, errors in sorted(classified.items()):
            lines.append(f"- **{etype}**: {len(errors)} errors")

    content = "\n".join(lines) + "\n"

    if not dry_run:
        report_path.write_text(content)
        print(f"Report written: {report_path}")
    else:
        print(f"[DRY RUN] Would write report to: {report_path}")
        print(content)


def main():
    parser = argparse.ArgumentParser(description="Upgrade Lean/mathlib toolchain")
    parser.add_argument("--target", help="Target version (e.g. v4.31.0)")
    parser.add_argument(
        "--latest", action="store_true", help="Use latest stable version"
    )
    parser.add_argument(
        "--latest-check",
        action="store_true",
        help="Only print latest version",
    )
    parser.add_argument(
        "--dry-run", action="store_true", help="Preview only"
    )
    args = parser.parse_args()

    if args.latest_check:
        latest = get_latest_stable_lean()
        if latest:
            print(latest)
        else:
            print("ERROR: Could not detect latest version", file=sys.stderr)
            sys.exit(1)
        return

    current = get_current_version()

    if args.target:
        target = args.target.lstrip("v")
    elif args.latest:
        target = get_latest_stable_lean()
        if target is None:
            print(
                "ERROR: Could not detect latest stable Lean version",
                file=sys.stderr,
            )
            sys.exit(1)
    else:
        parser.print_help()
        sys.exit(1)

    if target == current:
        print(f"Already at latest version: v{current}")
        return

    print(f"Upgrading: v{current} → v{target}")

    # Step 1: Create tag
    tag = f"toolchain-v{current}"
    if not args.dry_run:
        create_tag(current)
    else:
        print(f"[DRY RUN] Would create tag: {tag}")

    # Step 2: Update toolchain files
    if not args.dry_run:
        update_toolchain_files(target)
    else:
        print(f"[DRY RUN] Would update toolchain files to v{target}")

    # Step 3: Update dependencies
    if not args.dry_run:
        update_dependencies()
    else:
        print("[DRY RUN] Would run lake update")

    # Step 4: Build
    if not args.dry_run:
        success, stderr = build_all()
    else:
        success, stderr = True, ""
        print("[DRY RUN] Would run lake build")

    # Step 5: Classify errors
    classified = classify_errors(stderr) if not success else {}

    # Step 6: Generate report
    generate_report(current, target, tag, success, classified, args.dry_run)

    # Step 7: Exit
    if success:
        print("\nUpgrade successful.")
        print(f"   Tag: {tag}")
        print(f"   Next: run sync to update mapping toolchain versions")
    else:
        affected = list_affected_books(classified)
        print(f"\nBuild failed — {len(affected)} books affected.")
        print(f"   Report: docs/upgrade-reports/v{target}.md")
        print(f"   Next: run error-fix workflow to address safe errors, then manual review")
        sys.exit(1)


if __name__ == "__main__":
    main()
