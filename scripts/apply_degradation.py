#!/usr/bin/env python3
"""Preview or apply one explicitly approved local degradation proposal."""

from __future__ import annotations

import argparse
import json
import os
import re
import subprocess
import sys
from datetime import datetime, timezone
from pathlib import Path

SCRIPT_DIR = Path(__file__).resolve().parent
sys.path.insert(0, str(SCRIPT_DIR))
from lib.project_scope import resolve

ROOT = Path(os.environ.get("REASBOOK_ROOT", SCRIPT_DIR.parent)).resolve()
PROJECT = ROOT / "ReasBook"
REPORTS = ROOT / "docs" / "automation-reports"


def locate(run_id: str) -> Path:
    matches = [path for path in REPORTS.glob(f"v*/{run_id}") if path.is_dir()]
    if len(matches) != 1:
        raise SystemExit(
            f"expected exactly one local report for run ID {run_id!r}; found {len(matches)}"
        )
    return matches[0]


def summary_status(path: Path) -> str | None:
    match = re.search(r"^- Status: `([^`]+)`", path.read_text(encoding="utf-8"), re.MULTILINE)
    return match.group(1) if match else None


def clean_metadata(value: str, label: str) -> str:
    if not value.strip() or "\n" in value or "\r" in value:
        raise SystemExit(f"{label} must be one non-empty line")
    return value.strip()


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--run-id", required=True)
    scope = parser.add_mutually_exclusive_group(required=True)
    scope.add_argument("--book")
    scope.add_argument("--paper")
    parser.add_argument("--module", action="append", default=[], help="approved closure module; repeat")
    parser.add_argument("--approve", action="store_true")
    parser.add_argument("--reason")
    parser.add_argument("--restore-when")
    parser.add_argument("--expires", help="review date or toolchain condition")
    args = parser.parse_args()
    spec = resolve(PROJECT, "book", args.book) if args.book else resolve(PROJECT, "paper", args.paper)

    source_dir = locate(args.run_id)
    if summary_status(source_dir / "summary.md") != "repair-incomplete":
        raise SystemExit("degradation is allowed only from a repair-incomplete run")
    source_proposal = json.loads(
        (source_dir / "degradation-proposal.json").read_text(encoding="utf-8")
    )
    if source_proposal.get("run_id") != args.run_id:
        raise SystemExit("run ID does not match proposal contents")
    project_proposal = source_proposal.get("projects", {}).get(spec.key)
    if not project_proposal:
        raise SystemExit(f"proposal has no entry for project {spec.key!r}")
    suggested = list(project_proposal.get("suggested_modules", []))
    stored_approval = list(project_proposal.get("approved_modules", []))
    selected = args.module or stored_approval

    print(f"run: {args.run_id}\nproject: {spec.key}")
    print(f"root modules: {len(project_proposal.get('root_modules', []))}")
    print(f"cascade modules: {len(project_proposal.get('cascade_modules', []))}")
    print(f"proposed closure: {len(suggested)}")
    for module in suggested:
        marker = "APPROVED" if module in selected else "PROPOSED"
        print(f"  [{marker}] {module}")
    if not args.approve:
        print("preview only; approval requires the exact closure and review metadata")
        return 0

    if set(selected) != set(suggested) or len(selected) != len(set(selected)):
        raise SystemExit("approved modules must equal the exact proposed reverse-dependency closure")
    if not selected:
        raise SystemExit("proposal has no modules to disable")
    if not args.reason or not args.restore_when or not args.expires:
        raise SystemExit("--approve requires --reason, --restore-when, and --expires")
    reason = clean_metadata(args.reason, "reason")
    restore_when = clean_metadata(args.restore_when, "restore condition")
    expires = clean_metadata(args.expires, "expiry")

    manifest_path = ROOT / "docs" / "degradations.json"
    try:
        manifest = json.loads(manifest_path.read_text(encoding="utf-8"))
        entries = manifest["entries"]
        if not isinstance(entries, list):
            raise ValueError("entries is not a list")
    except (OSError, json.JSONDecodeError, KeyError, ValueError) as error:
        raise SystemExit(f"invalid degradation manifest: {error}")

    entry = spec.entry
    original = entry.read_text(encoding="utf-8")
    remaining = set(selected)
    output: list[str] = []
    for line in original.splitlines():
        match = re.match(r"^(\s*)import\s+(\S+)\s*$", line)
        if match and match.group(2) in remaining:
            module = match.group(2)
            output.extend([
                f"-- MANUAL-DEGRADATION run={args.run_id} toolchain=v{source_proposal['toolchain']}",
                f"-- reason: {reason}; restore-when: {restore_when}; expires: {expires}",
                f"-- import {module}",
            ])
            remaining.remove(module)
        else:
            output.append(line)
    if remaining:
        raise SystemExit("approved modules not found as active imports: " + ", ".join(sorted(remaining)))
    entry.write_text("\n".join(output) + "\n", encoding="utf-8")

    build = subprocess.run(
        ["lake", "build", spec.target], cwd=PROJECT,
        text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, check=False,
    )
    if build.returncode:
        entry.write_text(original, encoding="utf-8")
    status = "manually-degraded" if build.returncode == 0 else "repair-incomplete"
    degraded_id = f"{args.run_id}-degraded-{datetime.now(timezone.utc):%Y%m%dT%H%M%SZ}"
    result_dir = source_dir.parent / degraded_id
    result_dir.mkdir(parents=False, exist_ok=False)
    (result_dir / "build-final.log").write_text(build.stdout, encoding="utf-8")

    if build.returncode == 0:
        approval_entry = {
            "kind": spec.kind,
            "name": spec.name,
            "modules": sorted(selected),
            "source_run_id": args.run_id,
            "toolchain": source_proposal["toolchain"],
            "reason": reason,
            "restore_when": restore_when,
            "expires": expires,
        }
        manifest["entries"] = [
            item for item in entries
            if not (item.get("kind") == spec.kind and item.get("name") == spec.name)
        ]
        manifest["entries"].append(approval_entry)
        manifest["entries"].sort(key=lambda item: (item["kind"], item["name"]))
        manifest_path.write_text(
            json.dumps(manifest, indent=2, ensure_ascii=False) + "\n", encoding="utf-8"
        )

    coverage_path = result_dir / "import-coverage.json"
    coverage = subprocess.run([
        sys.executable, str(SCRIPT_DIR / "verify_import_coverage.py"),
        f"--{spec.kind}", spec.name, "--json", str(coverage_path),
        "--approved-degradations", str(manifest_path),
        "--allow-approved-degradation",
    ], text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, check=False)
    diagnostics = {
        "source_run_id": args.run_id,
        "degraded_build_exit_code": build.returncode,
        "build_diagnostics": build.stdout,
        "import_coverage_exit_code": coverage.returncode,
        "import_coverage_output": coverage.stdout,
    }
    (result_dir / "diagnostics.json").write_text(
        json.dumps(diagnostics, indent=2, ensure_ascii=False) + "\n", encoding="utf-8"
    )
    (result_dir / "fixes.json").write_text(
        json.dumps({"automatic_repairs": [], "manual_degradation": selected}, indent=2) + "\n",
        encoding="utf-8",
    )
    result_proposal = {
        **source_proposal,
        "run_id": degraded_id,
        "source_run_id": args.run_id,
        "status": status,
        "applied": build.returncode == 0,
        "approval": {
            "kind": spec.kind,
            "name": spec.name,
            "modules": selected,
            "reason": reason,
            "restore_when": restore_when,
            "expires": expires,
        },
    }
    (result_dir / "degradation-proposal.json").write_text(
        json.dumps(result_proposal, indent=2, ensure_ascii=False) + "\n", encoding="utf-8"
    )
    summary = [
        f"# Manual degradation run {degraded_id}", "",
        f"- Status: `{status}`",
        f"- Source full-import run: `{args.run_id}`",
        f"- Project: `{spec.key}`",
        f"- Toolchain: `v{source_proposal['toolchain']}`",
        f"- Approved closure size: `{len(selected)}`",
        f"- Reason: {reason}",
        f"- Restore when: {restore_when}",
        f"- Review/expiry: {expires}",
        f"- Degraded subset build exit code: `{build.returncode}`", "",
        "This is a subset result and must not be interpreted as full-pass.", "",
    ]
    (result_dir / "summary.md").write_text("\n".join(summary), encoding="utf-8")
    print(f"result_run_id={degraded_id}\nstatus={status}\nreport={result_dir.relative_to(ROOT)}")
    return build.returncode


if __name__ == "__main__":
    sys.exit(main())
