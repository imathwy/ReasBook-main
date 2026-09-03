"""Command line interface for the standalone Verso build SDK."""

from __future__ import annotations

import argparse
import json
import shlex
import sys
from pathlib import Path

from .builder import VersoBuilder
from .config import VersoBuildConfig
from .errors import VersoBuildError


def _split_option(value: str | None) -> tuple[str, ...] | None:
    if value is None:
        return None
    return tuple(shlex.split(value))


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(
        prog="verso-build",
        description="Build a Verso site without platform-specific task dependencies.",
    )
    parser.add_argument("web_root", type=Path, help="Verso/Lake project root")
    parser.add_argument(
        "--toolchain", help="Lean toolchain (defaults to lean-toolchain)"
    )
    parser.add_argument("--lake-bin", help="Lake executable")
    parser.add_argument("--elan-bin", help="Elan executable")
    parser.add_argument(
        "--target",
        action="append",
        dest="targets",
        help="Lake argument after `lake` (repeatable; defaults to `exe reasbook-site`)",
    )
    parser.add_argument(
        "--generator",
        help="optional generator command, parsed as shell-like argv",
    )
    parser.add_argument("--generator-cwd", type=Path)
    parser.add_argument("--output-dir", type=Path)
    parser.add_argument(
        "--no-install-toolchain",
        action="store_true",
        help="do not ask Elan to install the pinned toolchain",
    )
    parser.add_argument(
        "--keep-lean-environment",
        action="store_true",
        help="preserve inherited Lake/Lean environment variables",
    )
    parser.add_argument("--verify-output", action="store_true")
    parser.add_argument(
        "--dry-run",
        action="store_true",
        help="print the plan without executing commands",
    )
    parser.add_argument(
        "--json", action="store_true", help="emit machine-readable output"
    )
    return parser


def main(argv: list[str] | None = None) -> int:
    args = build_parser().parse_args(argv)
    try:
        defaults = VersoBuildConfig.from_env(args.web_root)
        config = VersoBuildConfig(
            web_root=args.web_root,
            toolchain=args.toolchain
            if args.toolchain is not None
            else defaults.toolchain,
            lake_bin=args.lake_bin or defaults.lake_bin,
            elan_bin=args.elan_bin or defaults.elan_bin,
            targets=tuple(args.targets) if args.targets else defaults.targets,
            generator=(
                _split_option(args.generator)
                if args.generator is not None
                else defaults.generator
            ),
            generator_cwd=(
                args.generator_cwd
                if args.generator_cwd is not None
                else defaults.generator_cwd
            ),
            output_dir=(
                args.output_dir if args.output_dir is not None else defaults.output_dir
            ),
            install_toolchain=(
                False if args.no_install_toolchain else defaults.install_toolchain
            ),
            clean_lean_environment=(
                False if args.keep_lean_environment else defaults.clean_lean_environment
            ),
            verify_output=args.verify_output or defaults.verify_output,
            environment=defaults.environment,
        )
        builder = VersoBuilder(config)
        result = builder.run(dry_run=args.dry_run)
        if args.json:
            print(json.dumps(result.public_dict(), indent=2, sort_keys=True))
        else:
            action = "planned" if result.dry_run else "completed"
            print(f"[verso-build] {action} {len(result.commands)} stage(s)")
            for command in result.commands:
                print(f"[verso-build] {command.stage}: {shlex.join(command.argv)}")
        return 0
    except VersoBuildError as exc:
        print(f"[verso-build] error: {exc}", file=sys.stderr)
        return 2


__all__ = ["build_parser", "main"]
