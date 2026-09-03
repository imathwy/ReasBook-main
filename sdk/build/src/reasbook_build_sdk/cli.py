"""Command-line interface for planning and running local Lean builds."""

from __future__ import annotations

import argparse
import json
import os
import sys
from pathlib import Path

from .command import CommandExecutionError
from .config import load_build_options
from .docs import ProjectDocumentationBuilder
from .errors import BuildSdkError
from .models import BuildPlan, BuildResult
from .lake import cache_command
from .service import BuildService
from .executor import SubprocessRunner
from .targets import project_doc_targets, selected_targets


def _parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(
        prog="reasbook-build",
        description="Plan and execute a reproducible Lean Lake build.",
    )
    commands = parser.add_subparsers(dest="command", required=True)

    for name, help_text in (
        ("build", "execute a build plan"),
        ("plan", "print a build plan without executing it"),
        ("cache", "run only the Lake cache preflight"),
    ):
        command = commands.add_parser(name, help=help_text)
        command.add_argument("project", type=Path, help="path to the Lake project")
        command.add_argument("targets", nargs="*", help="optional Lake targets")
        command.add_argument("--target", action="append", help="add one Lake target")
        command.add_argument(
            "--lake-arg",
            action="append",
            help="argument inserted before the Lake subcommand",
        )
        command.add_argument("--lake-bin", help="Lake executable (default: lake)")
        command.add_argument(
            "--skip-cache-get", action="store_true", help="skip cache preflight"
        )
        command.add_argument("--cache-timeout-seconds", type=float)
        command.add_argument("--build-timeout-seconds", type=float)
        command.add_argument(
            "--env", dest="build_env", action="append", metavar="KEY=VALUE"
        )
        command.add_argument("--mathlib-cache-dir")
        command.add_argument("--xdg-cache-home")
        command.add_argument("--no-verify-outputs", action="store_true")
        command.add_argument(
            "--artifact-extensions", help="comma-separated extensions to verify"
        )
        command.add_argument(
            "--json", action="store_true", help="emit machine-readable output"
        )
        if name == "build":
            command.add_argument(
                "--dry-run",
                action="store_true",
                help="show the plan without running commands",
            )
    targets = commands.add_parser(
        "targets", help="resolve ReasBook project modules from a Lake file"
    )
    targets.add_argument("project", type=Path, help="path to the Lake project")
    targets.add_argument(
        "--mode", choices=("project-docs", "selected"), default="project-docs"
    )
    targets.add_argument("--projects-json")
    targets.add_argument("--no-docs", action="store_true")
    targets.add_argument("--books-only", action="store_true")
    project_docs = commands.add_parser(
        "project-docs",
        help="generate bounded API docs for reachable project modules",
    )
    project_docs.add_argument("project", type=Path, help="path to the Lake project")
    project_docs.add_argument("targets", nargs="+", help="root Lean modules")
    project_docs.add_argument("--output", type=Path, required=True)
    project_docs.add_argument("--lake-bin", default="lake")
    project_docs.add_argument("--repository", default="")
    project_docs.add_argument("--revision", default="")
    project_docs.add_argument("--timeout-seconds", type=float, default=21600.0)
    project_docs.add_argument("--json", action="store_true")
    return parser


def _plan_payload(plan: BuildPlan) -> dict[str, object]:
    return plan.public_dict()


def _result_payload(result: BuildResult) -> dict[str, object]:
    return result.public_dict()


def _normalize_lake_arg_tokens(values: list[str]) -> list[str]:
    """Allow the natural ``--lake-arg -R`` spelling for dash-prefixed flags."""

    normalized: list[str] = []
    index = 0
    while index < len(values):
        value = values[index]
        if value == "--lake-arg" and index + 1 < len(values):
            candidate = values[index + 1]
            if candidate.startswith("-"):
                normalized.append(f"--lake-arg={candidate}")
                index += 2
                continue
        normalized.append(value)
        index += 1
    return normalized


def _print_plan(plan: BuildPlan, *, as_json: bool) -> None:
    if as_json:
        print(json.dumps(_plan_payload(plan), ensure_ascii=True, indent=2))
        return
    print(f"project: {plan.project.root}")
    print(f"toolchain: {plan.project.toolchain}")
    print(f"targets: {plan.target_label}")
    for index, command in enumerate(plan.commands, start=1):
        print(f"{index}. (cd {command.cwd}) {command.display}")


def _print_result(result: BuildResult, *, as_json: bool) -> None:
    if as_json:
        print(json.dumps(_result_payload(result), ensure_ascii=True, indent=2))
    else:
        print(result.summary())
        for snapshot in result.command_results:
            print(f"  {snapshot.command.display}: exit {snapshot.returncode}")
        for artifact in result.artifacts:
            print(f"  artifact: {artifact}")


def _print_targets(args: argparse.Namespace) -> int:
    if args.mode == "project-docs":
        targets = project_doc_targets(args.project, include_papers=not args.books_only)
    else:
        raw = args.projects_json
        if raw is None:
            raw = os.environ.get("PROJECTS_JSON", "[]")
        try:
            projects = json.loads(raw)
        except json.JSONDecodeError as exc:
            raise ValueError(f"PROJECTS_JSON is not valid JSON: {exc}") from exc
        if not isinstance(projects, list):
            raise ValueError("PROJECTS_JSON must be a JSON array")
        targets = selected_targets(
            args.project, projects, include_docs=not args.no_docs
        )
    print("\n".join(targets))
    return 0


def main(argv: list[str] | None = None) -> int:
    raw_argv = list(sys.argv[1:] if argv is None else argv)
    args = _parser().parse_args(_normalize_lake_arg_tokens(raw_argv))
    try:
        if args.command == "targets":
            return _print_targets(args)
        if args.command == "project-docs":
            result = ProjectDocumentationBuilder().build(
                args.project,
                args.targets,
                args.output,
                lake_bin=args.lake_bin,
                repository=args.repository,
                revision=args.revision,
                timeout_seconds=args.timeout_seconds,
            )
            if args.json:
                print(json.dumps(result.public_dict(), ensure_ascii=True, indent=2))
            else:
                disposition = "reused" if result.reused else "generated"
                print(
                    f"[reasbook-build] {disposition} {len(result.pages)} API "
                    f"page(s) from {len(result.targets)} project root(s) in "
                    f"{result.output_root}"
                )
            return 0
        positional_targets = list(getattr(args, "targets", []) or [])
        positional_targets.extend(getattr(args, "target", []) or [])
        options = load_build_options(args, targets=positional_targets)
        service = BuildService()
        if args.command == "cache":
            if not options.run_cache_get:
                if args.json:
                    print(
                        json.dumps(
                            {"status": "skipped", "reason": "cache preflight disabled"}
                        )
                    )
                else:
                    print("[reasbook-build] cache preflight skipped")
                return 0
            project = service.discover(args.project)
            command = cache_command(
                project,
                lake_bin=options.lake_bin,
                timeout_seconds=options.cache_timeout_seconds,
                lake_args=options.lake_args,
                targets=options.targets,
                environment=options.environment,
            )
            result = SubprocessRunner(stream=True).run(command)
            if args.json:
                print(
                    json.dumps(
                        {
                            "argv": list(result.argv),
                            "returncode": result.returncode,
                            "timed_out": result.timed_out,
                            "duration_seconds": result.duration_seconds,
                        },
                        indent=2,
                    )
                )
            return 0 if result.succeeded else 1
        if args.command == "plan":
            plan = service.plan(args.project, options)
            _print_plan(plan, as_json=bool(args.json))
            return 0
        result = service.run(args.project, options, dry_run=bool(args.dry_run))
        _print_result(result, as_json=bool(args.json))
        return 0 if result.succeeded or result.status == "dry_run" else 1
    except (BuildSdkError, CommandExecutionError, OSError, ValueError) as exc:
        print(f"reasbook-build: {exc}", file=sys.stderr)
        return 2 if isinstance(exc, (BuildSdkError, ValueError)) else 1


if __name__ == "__main__":  # pragma: no cover
    raise SystemExit(main())
