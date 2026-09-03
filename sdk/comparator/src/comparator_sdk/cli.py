"""Command-line interface for the local Comparator SDK."""

from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path

from .config import ComparatorConfig
from .errors import ComparatorError
from .runner import ComparatorRunner


def _env_values(values: list[str] | None) -> dict[str, str]:
    result: dict[str, str] = {}
    for raw in values or []:
        if "=" not in raw:
            raise ComparatorError(f"--env expects KEY=VALUE, got {raw!r}")
        key, value = raw.split("=", 1)
        result[key] = value
    return result


def _common_options(parser: argparse.ArgumentParser) -> None:
    parser.add_argument(
        "--comparator-root", type=Path, required=True, help="Comparator source checkout"
    )
    parser.add_argument("--lake-bin", help="Lake executable")
    parser.add_argument(
        "--comparator-lake-bin", help="Lake executable for the Comparator checkout"
    )
    parser.add_argument(
        "--comparator-bin", type=Path, help="prebuilt Comparator executable"
    )
    parser.add_argument("--landrun-bin", help="Landrun executable/path")
    parser.add_argument("--lean4export-bin", help="lean4export executable/path")
    parser.add_argument("--nanoda-bin", help="optional external-kernel executable/path")
    parser.add_argument(
        "--no-build", action="store_true", help="use an existing Comparator executable"
    )
    parser.add_argument(
        "--cache",
        action="store_true",
        help="run `lake exe cache get` before comparison",
    )
    parser.add_argument(
        "--cache-comparator",
        action="store_true",
        help="also warm the Comparator checkout",
    )
    parser.add_argument(
        "--timeout",
        type=float,
        help="comparison/build timeout in seconds",
    )
    parser.add_argument("--cache-timeout", type=float, help="cache preflight timeout")
    parser.add_argument("--sandbox-mode", choices=("direct", "systemd"))
    parser.add_argument(
        "--verify-outputs",
        action="store_true",
        help="require Challenge/Solution .olean files",
    )
    parser.add_argument("--result-file", type=Path, help="write a JSON result summary")
    parser.add_argument(
        "--env",
        action="append",
        metavar="KEY=VALUE",
        help="additional Comparator environment value",
    )
    parser.add_argument(
        "--no-lock", action="store_true", help="disable SDK project locks"
    )
    parser.add_argument(
        "--json", action="store_true", help="emit JSON instead of human-readable output"
    )


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(
        prog="comparator",
        description="Validate and run a Lean Comparator check locally.",
    )
    parser.add_argument("--version", action="version", version="comparator-sdk 0.1.0")
    subparsers = parser.add_subparsers(dest="command", required=True)
    compare = subparsers.add_parser("compare", help="prepare and run Comparator")
    compare.add_argument("project_root", type=Path)
    compare.add_argument("config_path", type=Path)
    _common_options(compare)
    compare.add_argument(
        "--dry-run",
        action="store_true",
        help="print the plan without executing commands",
    )

    validate = subparsers.add_parser(
        "validate", help="validate project and Comparator configuration"
    )
    validate.add_argument("project_root", type=Path)
    validate.add_argument("config_path", type=Path)
    validate.add_argument("--comparator-root", type=Path, required=True)
    validate.add_argument("--json", action="store_true")
    return parser


def _config(args: argparse.Namespace) -> ComparatorConfig:
    kwargs: dict[str, object] = {}
    for name in (
        "lake_bin",
        "comparator_lake_bin",
        "comparator_bin",
        "landrun_bin",
        "lean4export_bin",
        "nanoda_bin",
        "timeout_seconds",
        "cache_timeout_seconds",
        "sandbox_mode",
        "result_file",
    ):
        value = getattr(args, name, None)
        if value is not None:
            kwargs[name] = value
    if args.no_build:
        kwargs["build_comparator"] = False
    if args.cache:
        kwargs["cache_before_compare"] = True
    if args.cache_comparator:
        kwargs["cache_comparator"] = True
    if args.verify_outputs:
        kwargs["verify_outputs"] = True
    if args.no_lock:
        kwargs["lock"] = False
    environment = _env_values(args.env)
    if environment:
        kwargs["environment"] = environment
    return ComparatorConfig.from_env(
        args.project_root,
        args.config_path,
        args.comparator_root,
        **kwargs,
    )


def _print_result(result: object, *, as_json: bool) -> None:
    payload = result.public_dict()  # type: ignore[union-attr]
    if as_json:
        print(json.dumps(payload, ensure_ascii=False, indent=2, sort_keys=True))
        return
    status = payload["status"]
    detail = payload.get("error") or ""
    suffix = f": {detail}" if detail else ""
    print(f"[comparator] {status}{suffix}")
    if payload.get("stdout"):
        print(payload["stdout"], end="")
    if payload.get("stderr"):
        print(payload["stderr"], end="", file=sys.stderr)


def main(argv: list[str] | None = None) -> int:
    args = build_parser().parse_args(argv)
    try:
        if args.command == "validate":
            config = ComparatorConfig.from_paths(
                args.project_root,
                args.config_path,
                args.comparator_root,
                build_comparator=False,
            )
            payload = config.public_dict()
            if args.json:
                print(json.dumps(payload, indent=2, sort_keys=True))
            else:
                print(f"[comparator] valid project: {payload['project_root']}")
            return 0

        config = _config(args)
        result = ComparatorRunner(config).compare(dry_run=args.dry_run)
        _print_result(result, as_json=args.json)
        if result.status in {"accepted", "planned"}:
            return 0
        if result.status == "rejected":
            return 1
        if result.status == "timed_out":
            return 124
        return 2
    except ComparatorError as exc:
        print(f"[comparator] error: {exc}", file=sys.stderr)
        return 2
    except (OSError, ValueError) as exc:
        print(f"[comparator] error: {exc}", file=sys.stderr)
        return 2


__all__ = ["build_parser", "main"]
