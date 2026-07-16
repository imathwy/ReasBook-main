#!/usr/bin/env python3
"""Verify complete active imports for book Book.lean and paper Paper.lean entries."""

from __future__ import annotations

import argparse
import json
import os
import re
import sys
from collections import Counter
from pathlib import Path

SCRIPT_DIR = Path(__file__).resolve().parent
sys.path.insert(0, str(SCRIPT_DIR))
from lib.project_scope import ProjectSpec, discover, module_for, resolve, source_files

ROOT = Path(os.environ.get("REASBOOK_ROOT", SCRIPT_DIR.parent)).resolve()
PROJECT = ROOT / "ReasBook"
ACTIVE_RE = re.compile(r"^\s*import\s+([^\s]+)")
DISABLED_RE = re.compile(r"^\s*--\s*import\s+([^\s]+)")


def inspect_project(spec: ProjectSpec, approved: set[str] | None = None) -> dict:
    if not spec.entry.is_file():
        return {"kind": spec.kind, "name": spec.name, "error": f"{spec.entry_name} not found", "ok": False}
    expected = sorted(module_for(spec, path) for path in source_files(spec))
    active: list[str] = []
    disabled: list[str] = []
    for line in spec.entry.read_text(encoding="utf-8").splitlines():
        if match := ACTIVE_RE.match(line):
            module = match.group(1)
            if module != "Mathlib":
                active.append(module)
        elif match := DISABLED_RE.match(line):
            disabled.append(match.group(1))
    counts = Counter(active)
    expected_set, active_set = set(expected), set(active)
    result = {
        "kind": spec.kind,
        "name": spec.name,
        "entry": f"{'Books' if spec.kind == 'book' else 'Papers'}/{spec.name}/{spec.entry_name}",
        "target": spec.target,
        "source_count": len(expected),
        "active_import_count": len(active),
        "missing": sorted(expected_set - active_set),
        "extra": sorted(active_set - expected_set),
        "duplicates": sorted(key for key, value in counts.items() if value > 1),
        "disabled": sorted(set(disabled)),
        "approved_modules": sorted(approved or set()),
    }
    result["ok"] = not any(result[key] for key in ("missing", "extra", "duplicates", "disabled"))
    result["approved_degradation_ok"] = bool(approved) and (
        set(result["missing"]) == approved
        and set(result["disabled"]) == approved
        and not result["extra"]
        and not result["duplicates"]
    )
    result["stale_approval"] = bool(approved) and result["ok"]
    return result


def load_approvals(path: Path | None) -> dict[tuple[str, str], set[str]]:
    if path is None:
        return {}
    data = json.loads(path.read_text(encoding="utf-8"))
    approvals: dict[tuple[str, str], set[str]] = {}
    toolchain = (PROJECT / "lean-toolchain").read_text(encoding="utf-8").strip().rsplit(":v", 1)[-1]
    for entry in data.get("entries", []):
        kind, name, modules = entry.get("kind"), entry.get("name"), entry.get("modules")
        if kind not in {"book", "paper"} or not name or not isinstance(modules, list) or not modules:
            raise ValueError("every degradation entry needs kind, name, and non-empty modules")
        if len(modules) != len(set(modules)):
            raise ValueError(f"duplicate modules in degradation entry for {kind}:{name}")
        required = ("source_run_id", "toolchain", "reason", "restore_when", "expires")
        missing = [key for key in required if not entry.get(key)]
        if missing:
            raise ValueError(f"degradation entry for {kind}:{name} is missing {missing}")
        if str(entry["toolchain"]).removeprefix("v") != toolchain:
            raise ValueError(f"degradation entry for {kind}:{name} targets a different toolchain")
        key = (kind, name)
        if key in approvals:
            raise ValueError(f"duplicate degradation entry for {kind}:{name}")
        approvals[key] = set(modules)
    return approvals


def selected_specs(book: str | None, paper: str | None, all_projects: bool) -> list[ProjectSpec]:
    if book:
        return [resolve(PROJECT, "book", book)]
    if paper:
        return [resolve(PROJECT, "paper", paper)]
    if all_projects:
        return discover(PROJECT)
    raise ValueError("choose --book NAME, --paper NAME, or --all")


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    group = parser.add_mutually_exclusive_group(required=True)
    group.add_argument("--book")
    group.add_argument("--paper")
    group.add_argument("--all", action="store_true")
    parser.add_argument("--json", type=Path)
    parser.add_argument("--approved-degradations", type=Path)
    parser.add_argument("--allow-approved-degradation", action="store_true")
    args = parser.parse_args()
    try:
        approvals = load_approvals(args.approved_degradations)
        specs = selected_specs(args.book, args.paper, args.all)
    except (OSError, json.JSONDecodeError, ValueError) as error:
        print(f"invalid coverage input: {error}", file=sys.stderr)
        return 2
    selected_keys = {(spec.kind, spec.name) for spec in specs}
    unknown = sorted(f"{kind}:{name}" for kind, name in set(approvals) - selected_keys) if args.all else []
    results = [inspect_project(spec, approvals.get((spec.kind, spec.name))) for spec in specs]
    standard_ok = all(result["ok"] for result in results)
    manifest_consistent = not unknown and not any(result.get("stale_approval") for result in results)
    approved_ok = manifest_consistent and all(
        (result["ok"] and not result["approved_modules"]) or result["approved_degradation_ok"]
        for result in results
    )
    payload = {
        "ok": standard_ok,
        "approved_ok": approved_ok,
        "manifest_consistent": manifest_consistent,
        "allow_approved_degradation": args.allow_approved_degradation,
        "unknown_manifest_projects": unknown,
        "projects": results,
    }
    if args.json:
        args.json.parent.mkdir(parents=True, exist_ok=True)
        args.json.write_text(json.dumps(payload, indent=2, ensure_ascii=False) + "\n", encoding="utf-8")
    for result in results:
        state = "PASS" if result["ok"] else "FAIL"
        print(f"{state} {result['kind']}:{result['name']}: "
              f"{result.get('source_count', 0)} source / {result.get('active_import_count', 0)} active")
        for key in ("missing", "extra", "duplicates", "disabled"):
            if result.get(key):
                print(f"  {key}: {', '.join(result[key])}")
        if result.get("error"):
            print(f"  error: {result['error']}")
        if result.get("approved_degradation_ok"):
            print("  approved degradation manifest: exact match")
        if result.get("stale_approval"):
            print("  stale degradation approval: imports are active; remove the manifest entry")
    accepted = (standard_ok and manifest_consistent) or (
        args.allow_approved_degradation and approved_ok
    )
    return 0 if accepted else 1


if __name__ == "__main__":
    sys.exit(main())
