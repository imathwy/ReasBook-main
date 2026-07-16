#!/usr/bin/env python3
"""Run full-import Lean validation and write one local, auditable report."""

from __future__ import annotations

import argparse
from collections import Counter
import hashlib
import json
import os
import re
import subprocess
import sys
from datetime import datetime, timezone
from pathlib import Path

SCRIPT_DIR = Path(__file__).resolve().parent
sys.path.insert(0, str(SCRIPT_DIR))
from lib.project_scope import ProjectSpec, discover, module_for, resolve, source_files

ROOT = Path(os.environ.get("REASBOOK_ROOT", SCRIPT_DIR.parent)).resolve()
PROJECT = ROOT / "ReasBook"
REPORTS = ROOT / "docs" / "automation-reports"
ERROR_RES = (
    re.compile(
        r"(?:^|\s)error:\s*(?P<file>[^\s:]+\.lean):(?P<line>\d+):"
        r"(?P<column>\d+):\s*(?P<message>.*)"
    ),
    re.compile(
        r"(?P<file>[^\s:]+\.lean):(?P<line>\d+):(?P<column>\d+):"
        r"\s*error:\s*(?P<message>.*)"
    ),
)
BYPASS_RE = re.compile(r"\b(sorry|admit|axiom)\b")
RUN_ID_RE = re.compile(r"^[A-Za-z0-9][A-Za-z0-9._-]*$")
INFRA_RE = re.compile(
    r"unknown target|no space left|network is unreachable|could not resolve host|"
    r"connection timed out|connection refused|permission denied|command not found|"
    r"failed to fetch|missing manifest|invalid manifest",
    re.IGNORECASE,
)


def run(command: list[str], cwd: Path = ROOT) -> subprocess.CompletedProcess[str]:
    return subprocess.run(
        command, cwd=cwd, text=True, stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT, check=False,
    )


def current_toolchain() -> str:
    text = (PROJECT / "lean-toolchain").read_text(encoding="utf-8").strip()
    return text.rsplit(":v", 1)[-1]


def git_value(*args: str) -> str:
    result = run(["git", *args])
    return result.stdout.strip() if result.returncode == 0 else "unknown"


def target_revision() -> str:
    """Return HEAD when clean, otherwise a reproducible worktree fingerprint."""
    head = git_value("rev-parse", "HEAD")
    status = run(["git", "status", "--porcelain=v1", "--untracked-files=all"])
    if status.returncode != 0 or not status.stdout.strip():
        return head
    digest = hashlib.sha256()
    digest.update(run(["git", "diff", "--binary", "HEAD"]).stdout.encode())
    untracked = run(["git", "ls-files", "--others", "--exclude-standard", "-z"])
    for name in sorted(filter(None, untracked.stdout.split("\0"))):
        digest.update(name.encode())
        path = ROOT / name
        if path.is_file():
            digest.update(path.read_bytes())
    return f"worktree@{head}:{digest.hexdigest()[:16]}"


def mathlib_revision() -> str:
    manifest = PROJECT / "lake-manifest.json"
    try:
        data = json.loads(manifest.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError):
        return "unknown"
    for package in data.get("packages", []):
        if package.get("name") == "mathlib":
            return package.get("rev") or package.get("version") or "unknown"
    return "unknown"


def parse_diagnostics(output: str) -> list[dict[str, str]]:
    diagnostics = []
    for line in output.splitlines():
        for pattern in ERROR_RES:
            if match := pattern.search(line):
                diagnostics.append(match.groupdict())
                break
    return diagnostics


def diagnostic_project(file_name: str) -> tuple[ProjectSpec, str] | None:
    normalized = file_name.replace("\\", "/")
    match = re.search(r"(?:^|/)(Books|Papers)/([^/]+)/(.+\.lean)$", normalized)
    if not match:
        return None
    area, name, relative = match.groups()
    spec = resolve(PROJECT, "book" if area == "Books" else "paper", name)
    return spec, module_for(spec, spec.directory / relative)


def module_graph(spec: ProjectSpec) -> tuple[dict[str, set[str]], dict[str, set[str]]]:
    """Return same-project dependency and reverse-dependency graphs."""
    modules: dict[str, Path] = {}
    for path in source_files(spec):
        modules[module_for(spec, path)] = path
    dependencies = {module: set() for module in modules}
    imported_by = {module: set() for module in modules}
    import_re = re.compile(r"^\s*import\s+(\S+)", re.MULTILINE)
    for owner, path in modules.items():
        content = path.read_text(encoding="utf-8", errors="replace")
        for dependency in import_re.findall(content):
            if dependency in imported_by:
                dependencies[owner].add(dependency)
                imported_by[dependency].add(owner)
    return dependencies, imported_by


def degradation_closure(spec: ProjectSpec, root_modules: list[str]) -> list[str]:
    """Return roots plus all same-project reverse dependencies."""
    _, imported_by = module_graph(spec)
    closure = set(root_modules) & imported_by.keys()
    pending = list(closure)
    while pending:
        for owner in imported_by[pending.pop()]:
            if owner not in closure:
                closure.add(owner)
                pending.append(owner)
    return sorted(closure)


def coverage_run(
    selection: list[str], destination: Path, allow_approved: bool,
) -> tuple[int, dict, str]:
    temporary = destination.with_suffix(".tmp.json")
    command = [
        sys.executable, str(SCRIPT_DIR / "verify_import_coverage.py"),
        *selection, "--json", str(temporary),
    ]
    manifest = ROOT / "docs" / "degradations.json"
    if manifest.exists():
        command.extend(["--approved-degradations", str(manifest)])
    if allow_approved:
        command.append("--allow-approved-degradation")
    result = run(command)
    try:
        payload = json.loads(temporary.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError):
        payload = {"ok": False, "projects": [], "infrastructure_error": result.stdout}
    temporary.unlink(missing_ok=True)
    return result.returncode, payload, result.stdout


def diff_arguments() -> list[str]:
    worktree = run(["git", "status", "--porcelain=v1", "--untracked-files=all"])
    if worktree.returncode == 0 and worktree.stdout.strip():
        return []
    base_ref = os.environ.get("GITHUB_BASE_REF")
    if base_ref and run(["git", "rev-parse", "--verify", f"origin/{base_ref}"]).returncode == 0:
        return [f"origin/{base_ref}...HEAD"]
    if os.environ.get("CI") and run(["git", "rev-parse", "--verify", "HEAD^"]).returncode == 0:
        return ["HEAD^...HEAD"]
    return []


def audit_paths(selected: ProjectSpec | None) -> list[str]:
    """Return the repository pathspec for a scoped run, or all Lean files."""
    if selected:
        return [str(selected.directory.relative_to(ROOT))]
    return ["*.lean"]


def proof_bypass_audit(diff_range: list[str], paths: list[str]) -> list[str]:
    diff = run(["git", "diff", "--unified=0", *diff_range, "--", *paths])
    lines = diff.stdout.splitlines()
    removed = Counter(
        match.group(1)
        for line in lines
        if line.startswith("-") and not line.startswith("---")
        for match in BYPASS_RE.finditer(line)
    )
    findings = []
    for line in lines:
        if not line.startswith("+") or line.startswith("+++"):
            continue
        unmatched = False
        for match in BYPASS_RE.finditer(line):
            keyword = match.group(1)
            if removed[keyword] > 0:
                removed[keyword] -= 1
            else:
                unmatched = True
        if unmatched:
            findings.append(line)
    untracked = run(["git", "ls-files", "--others", "--exclude-standard", "--", *paths])
    for name in untracked.stdout.splitlines():
        path = ROOT / name
        for number, line in enumerate(path.read_text(encoding="utf-8", errors="replace").splitlines(), 1):
            if BYPASS_RE.search(line):
                findings.append(f"{name}:{number}:{line}")
    return findings


def diff_check_audit(
    diff_range: list[str], paths: list[str],
) -> subprocess.CompletedProcess[str]:
    """Run Git's check and include untracked text files Git diff omits."""
    tracked = run(["git", "diff", "--check", *diff_range, "--", *paths])
    findings = [tracked.stdout] if tracked.stdout else []
    untracked = run(["git", "ls-files", "--others", "--exclude-standard", "--", *paths])
    for name in untracked.stdout.splitlines():
        path = ROOT / name
        if not path.is_file():
            continue
        try:
            lines = path.read_text(encoding="utf-8").splitlines()
        except (OSError, UnicodeDecodeError):
            continue
        for number, line in enumerate(lines, 1):
            if line.endswith((" ", "\t")):
                findings.append(f"{name}:{number}: trailing whitespace\n")
    output = "".join(findings)
    return subprocess.CompletedProcess(
        ["git", "diff", "--check", *diff_range, "--", *paths],
        tracked.returncode if tracked.returncode > 1 else (1 if tracked.returncode or output else 0),
        output,
    )


def build_proposals(run_id: str, diagnostics: list[dict], selected: ProjectSpec | None) -> dict:
    diagnosed_by_project: dict[str, tuple[ProjectSpec, dict[str, set[str]]]] = {}
    for diagnostic in diagnostics:
        resolved = diagnostic_project(diagnostic["file"])
        if not resolved:
            continue
        spec, module = resolved
        if spec.key not in diagnosed_by_project:
            diagnosed_by_project[spec.key] = (spec, {})
        diagnosed_by_project[spec.key][1].setdefault(module, set()).add(diagnostic["file"])
    projects = {}
    for key, (spec, module_files) in sorted(diagnosed_by_project.items()):
        diagnosed = set(module_files)
        dependencies, _ = module_graph(spec)

        def reaches_other_failure(module: str) -> bool:
            seen, pending = set(), list(dependencies.get(module, set()))
            while pending:
                dependency = pending.pop()
                if dependency in seen:
                    continue
                seen.add(dependency)
                if dependency in diagnosed:
                    return True
                pending.extend(dependencies.get(dependency, set()))
            return False

        roots = sorted(module for module in diagnosed if not reaches_other_failure(module))
        if not roots:
            roots = sorted(diagnosed)
        closure = degradation_closure(spec, roots)
        projects[key] = {
            "kind": spec.kind,
            "name": spec.name,
            "entry": spec.entry_name,
            "target": spec.target,
            "all_diagnostic_files": sorted({file for files in module_files.values() for file in files}),
            "diagnostic_modules": sorted(diagnosed),
            "root_failure_files": sorted({file for module in roots for file in module_files[module]}),
            "root_modules": roots,
            "cascade_modules": sorted(set(closure) - set(roots)),
            "suggested_modules": closure,
            "approved_modules": [],
        }
    return {
        "run_id": run_id,
        "toolchain": current_toolchain(),
        "status": "proposal-only",
        "projects": projects,
        "applied": False,
    }


def classify_status(
    preflight_exit: int, build_exit: int, diagnostics: list[dict],
    build_output: str, coverage_exit: int, coverage_infrastructure: bool,
    bypasses: list[str], diff_exit: int, approved_degraded: bool,
) -> str:
    if preflight_exit != 0:
        return "infrastructure-failure"
    if coverage_infrastructure or diff_exit > 1:
        return "infrastructure-failure"
    if build_exit != 0 and (not diagnostics or INFRA_RE.search(build_output)):
        return "infrastructure-failure"
    if build_exit == 0 and coverage_exit == 0 and not bypasses and diff_exit == 0:
        return "manually-degraded" if approved_degraded else "full-pass"
    return "repair-incomplete"


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    scope = parser.add_mutually_exclusive_group(required=True)
    scope.add_argument("--book")
    scope.add_argument("--paper")
    scope.add_argument("--all", action="store_true")
    parser.add_argument("--run-id")
    parser.add_argument("--repair", action="store_true")
    parser.add_argument("--trigger", default="manual")
    parser.add_argument("--source-commit", default=None)
    parser.add_argument("--preflight-exit-code", type=int, default=0)
    parser.add_argument("--preflight-log", type=Path)
    parser.add_argument("--tip-candidate", type=Path, action="append", default=[])
    parser.add_argument("--allow-approved-degradation", action="store_true")
    args = parser.parse_args()

    head_commit = git_value("rev-parse", "HEAD")
    short_commit = head_commit[:8] if head_commit != "unknown" else "unknown"
    run_id = args.run_id or f"{datetime.now(timezone.utc):%Y%m%dT%H%M%SZ}-{args.trigger}-{short_commit}"
    if not RUN_ID_RE.fullmatch(run_id):
        parser.error("--run-id may contain only letters, digits, dot, underscore, and hyphen")
    out_dir = REPORTS / f"v{current_toolchain()}" / run_id
    out_dir.mkdir(parents=True, exist_ok=False)
    selected = (
        resolve(PROJECT, "book", args.book) if args.book else
        resolve(PROJECT, "paper", args.paper) if args.paper else None
    )
    selection = [f"--{selected.kind}", selected.name] if selected else ["--all"]

    initial_cov_exit, initial_coverage, initial_cov_output = coverage_run(
        selection, out_dir / "import-coverage.json", args.allow_approved_degradation,
    )
    build_command = ["lake", "build", selected.target] if selected else [str(SCRIPT_DIR / "build_reasbook_core.sh")]
    preflight_output = ""
    if args.preflight_log:
        try:
            preflight_output = args.preflight_log.read_text(encoding="utf-8", errors="replace")
        except OSError as error:
            preflight_output = f"could not read preflight log: {error}"
    if args.preflight_exit_code:
        initial_build = subprocess.CompletedProcess(
            build_command, args.preflight_exit_code, preflight_output
        )
    else:
        initial_build = run(build_command, PROJECT)
    (out_dir / "build-initial.log").write_text(initial_build.stdout, encoding="utf-8")
    initial_diagnostics = parse_diagnostics(initial_build.stdout)

    repair_runs = []
    if args.repair and initial_build.returncode and not args.preflight_exit_code:
        diagnosed_projects = sorted({
            item[0] for diagnostic in initial_diagnostics
            if (item := diagnostic_project(diagnostic["file"]))
        }, key=lambda spec: spec.key)
        repair_projects = diagnosed_projects or ([selected] if selected else [])
        for spec in repair_projects:
            repair = run([
                sys.executable, str(SCRIPT_DIR / "fix_errors.py"),
                "--bootstrap", spec.name, "--kind", spec.kind,
                "--apply", "--output-dir", str(out_dir),
            ])
            repair_runs.append({
                "kind": spec.kind, "name": spec.name,
                "exit_code": repair.returncode, "output": repair.stdout,
            })

    final_build = run(build_command, PROJECT) if repair_runs else initial_build
    (out_dir / "build-final.log").write_text(final_build.stdout, encoding="utf-8")
    final_diagnostics = parse_diagnostics(final_build.stdout)
    final_cov_exit, final_coverage, final_cov_output = coverage_run(
        selection, out_dir / "import-coverage.json", args.allow_approved_degradation,
    )
    coverage_payload = {
        "initial_exit_code": initial_cov_exit,
        "final_exit_code": final_cov_exit,
        "initial": initial_coverage,
        "final": final_coverage,
        "initial_output": initial_cov_output,
        "final_output": final_cov_output,
    }
    (out_dir / "import-coverage.json").write_text(
        json.dumps(coverage_payload, indent=2, ensure_ascii=False) + "\n", encoding="utf-8"
    )

    diff_range = diff_arguments()
    paths = audit_paths(selected)
    bypasses = proof_bypass_audit(diff_range, paths)
    diff_check = diff_check_audit(diff_range, paths)
    proposals = build_proposals(run_id, final_diagnostics, selected)
    (out_dir / "degradation-proposal.json").write_text(
        json.dumps(proposals, indent=2, ensure_ascii=False) + "\n", encoding="utf-8"
    )
    diagnostics_payload = {
        "preflight_exit_code": args.preflight_exit_code,
        "preflight_output": preflight_output,
        "initial_build_exit_code": initial_build.returncode,
        "final_build_exit_code": final_build.returncode,
        "initial": initial_diagnostics,
        "final": final_diagnostics,
        "root_modules_by_project": {
            key: data["root_modules"] for key, data in proposals["projects"].items()
        },
        "cascade_modules_by_project": {
            key: data["cascade_modules"] for key, data in proposals["projects"].items()
        },
        "proof_bypass_findings": bypasses,
        "diff_check_exit_code": diff_check.returncode,
        "diff_check_output": diff_check.stdout,
    }
    (out_dir / "diagnostics.json").write_text(
        json.dumps(diagnostics_payload, indent=2, ensure_ascii=False) + "\n", encoding="utf-8"
    )
    approved_degraded = (
        args.allow_approved_degradation
        and not final_coverage.get("ok", False)
        and final_coverage.get("approved_ok", False)
    )
    status = classify_status(
        args.preflight_exit_code, final_build.returncode, final_diagnostics,
        final_build.stdout, final_cov_exit, "infrastructure_error" in final_coverage,
        bypasses, diff_check.returncode, approved_degraded,
    )
    compatibility_updates = []
    for candidate in args.tip_candidate:
        if status != "full-pass":
            compatibility_updates.append({
                "candidate": str(candidate), "status": "skipped",
                "reason": "automation run is not full-pass",
            })
            continue
        update = run([
            sys.executable, str(SCRIPT_DIR / "update_compatibility_tips.py"), str(candidate),
        ])
        compatibility_updates.append({
            "candidate": str(candidate), "status": "applied" if update.returncode == 0 else "rejected",
            "exit_code": update.returncode, "output": update.stdout,
        })
        if update.returncode:
            status = "repair-incomplete"
    fixes_payload = {
        "requested": args.repair,
        "runs": repair_runs,
        "compatibility_updates": compatibility_updates,
    }
    (out_dir / "fixes.json").write_text(
        json.dumps(fixes_payload, indent=2, ensure_ascii=False) + "\n", encoding="utf-8"
    )
    source_commit = args.source_commit or git_value("merge-base", "HEAD", "origin/main")
    if source_commit == "unknown":
        source_commit = head_commit
    target_commit = target_revision()
    root_count = sum(len(data["root_modules"]) for data in proposals["projects"].values())
    cascade_count = sum(len(data["cascade_modules"]) for data in proposals["projects"].values())
    summary = [
        f"# Automation run {run_id}", "",
        f"- Status: `{status}`",
        f"- Trigger: `{args.trigger}`",
        f"- Source commit: `{source_commit}`",
        f"- Target commit: `{target_commit}`",
        f"- Toolchain: `v{current_toolchain()}`",
        f"- Mathlib revision: `{mathlib_revision()}`",
        f"- Scope: `{selected.key if selected else 'all'}`",
        f"- Initial import coverage: `{'pass' if initial_cov_exit == 0 else 'fail'}`",
        f"- Final import coverage: `{'pass' if final_cov_exit == 0 else 'fail'}`",
        f"- Initial build exit code: `{initial_build.returncode}`",
        f"- Final build exit code: `{final_build.returncode}`",
        f"- Final root failure modules: `{root_count}`",
        f"- Proposed cascade modules: `{cascade_count}`",
        f"- Added proof bypass findings: `{len(bypasses)}`",
        f"- `git diff --check`: `{'pass' if diff_check.returncode == 0 else 'fail'}`",
        "",
        "The degradation proposal is advisory and has not been applied.", "",
    ]
    (out_dir / "summary.md").write_text("\n".join(summary), encoding="utf-8")
    (out_dir.parent / "latest.md").write_text(
        f"# Latest automation run\n\n- Run ID: `{run_id}`\n- Status: `{status}`\n"
        f"- Report: `{run_id}/summary.md`\n",
        encoding="utf-8",
    )
    print(f"run_id={run_id}\nstatus={status}\nreport={out_dir.relative_to(ROOT)}")
    if status in {"full-pass", "manually-degraded"}:
        return 0
    if args.preflight_exit_code:
        return args.preflight_exit_code
    return final_build.returncode or final_cov_exit or diff_check.returncode or 1


if __name__ == "__main__":
    sys.exit(main())
