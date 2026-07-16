#!/usr/bin/env python3
"""Validate authoritative documentation and optional local agent routing files."""

from __future__ import annotations

import argparse
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
REQUIRED_SHARED = [
    "docs/outline.md",
    "docs/workflow/automation-workflow.md",
    "docs/workflow/manual-degradation-workflow.md",
    "docs/workflow/script-and-ci-reference.md",
    "docs/compatibility/README.md",
    "docs/automation-reports/README.md",
    "scripts/verify_import_coverage.py",
    "scripts/run_automation.py",
    "scripts/apply_degradation.py",
    "scripts/update_compatibility_tips.py",
]
LOCAL_SKILLS = [
    "reasbook-automation",
    "reasbook-lean-repair",
    "reasbook-report-review",
]
PATH_RE = re.compile(r"`((?:docs|scripts|\.agents|\.github)/[^`\s]+|AGENTS\.md)`")


def referenced_paths(path: Path) -> list[str]:
    return [match.rstrip(".,;:)") for match in PATH_RE.findall(path.read_text(encoding="utf-8"))]


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--allow-missing-local", action="store_true",
        help="allow Git-ignored AGENTS.md and skills to be absent in a clean CI clone",
    )
    args = parser.parse_args()
    errors: list[str] = []
    for name in REQUIRED_SHARED:
        if not (ROOT / name).is_file():
            errors.append(f"missing shared entry: {name}")
    for name in REQUIRED_SHARED[:6]:
        path = ROOT / name
        if not path.is_file():
            continue
        for reference in referenced_paths(path):
            if "<" not in reference and "..." not in reference and not (ROOT / reference).exists():
                errors.append(f"{name} has missing reference: {reference}")

    toolchain = (ROOT / "ReasBook" / "lean-toolchain").read_text(encoding="utf-8").strip().rsplit(":v", 1)[-1]
    compatibility = ROOT / "docs" / "compatibility" / f"v{toolchain}.md"
    if not compatibility.is_file():
        errors.append(f"missing current compatibility document: {compatibility.relative_to(ROOT)}")

    agents = ROOT / "AGENTS.md"
    local_present = agents.is_file()
    if not local_present and not args.allow_missing_local:
        errors.append("missing local AGENTS.md")
    if local_present:
        for reference in referenced_paths(agents):
            if "<" not in reference and not (ROOT / reference).exists():
                errors.append(f"AGENTS.md has missing reference: {reference}")

    for skill_name in LOCAL_SKILLS:
        skill = ROOT / ".agents" / "skills" / skill_name / "SKILL.md"
        if not skill.is_file():
            if not args.allow_missing_local:
                errors.append(f"missing local skill: {skill_name}")
            continue
        text = skill.read_text(encoding="utf-8")
        if not text.startswith("---\n") or f"name: {skill_name}\n" not in text:
            errors.append(f"invalid skill frontmatter: {skill_name}")
        for reference in referenced_paths(skill):
            if "<" not in reference and "..." not in reference and not (ROOT / reference).exists():
                errors.append(f"{skill_name} has missing reference: {reference}")

    nested_agents = []
    for path in ROOT.rglob("AGENTS.md"):
        relative = path.relative_to(ROOT)
        if path == agents or ".lake" in relative.parts or relative.parts[0] == "ReasBookWeb":
            continue
        nested_agents.append(str(relative))
    if nested_agents:
        errors.append("unexpected nested AGENTS.md: " + ", ".join(nested_agents))

    for area in (ROOT / "scripts", ROOT / ".github" / "workflows", ROOT / ".agents" / "skills"):
        for path in area.rglob("*"):
            if path == Path(__file__).resolve():
                continue
            if path.is_file() and "docs/plan" in path.read_text(encoding="utf-8", errors="ignore"):
                errors.append(f"automation references protected docs/plan: {path.relative_to(ROOT)}")

    if errors:
        print("agent/document reference validation failed:", file=sys.stderr)
        for error in errors:
            print(f"- {error}", file=sys.stderr)
        return 1
    print("agent/document references: pass")
    return 0


if __name__ == "__main__":
    sys.exit(main())
