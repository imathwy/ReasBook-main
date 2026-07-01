"""Command-line interface for deterministic Phase 0 checks."""

from __future__ import annotations

import argparse
import json
from pathlib import Path

from .placeholders import scan_placeholders
from .policy import WritePolicy
from .records import validate_record
from .sandbox import sandbox_command
from .snapshot import tree_digest


def _parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(prog="optimization-harness")
    subparsers = parser.add_subparsers(dest="command", required=True)

    policy = subparsers.add_parser("policy-check")
    policy.add_argument("--repository-root", type=Path, required=True)
    policy.add_argument("--writable-root", type=Path, required=True)
    policy.add_argument("path", type=Path)

    snapshot = subparsers.add_parser("snapshot")
    snapshot.add_argument("root", type=Path)

    schema = subparsers.add_parser("validate-record")
    schema.add_argument("kind")
    schema.add_argument("record", type=Path)

    placeholders = subparsers.add_parser("scan-placeholders")
    placeholders.add_argument("root", type=Path)

    sandbox = subparsers.add_parser("sandbox-command")
    sandbox.add_argument("--repository-root", type=Path, required=True)
    sandbox.add_argument("--writable-root", type=Path, required=True)
    sandbox.add_argument("--working-directory", type=Path, required=True)
    sandbox.add_argument("--network", action="store_true")
    sandbox.add_argument("task_command", nargs=argparse.REMAINDER)
    return parser


def main() -> int:
    args = _parser().parse_args()
    if args.command == "policy-check":
        decision = WritePolicy(args.repository_root, args.writable_root).decide(args.path)
        print(json.dumps(decision.__dict__, indent=2))
        return 0 if decision.decision == "allow" else 2
    if args.command == "snapshot":
        print(json.dumps(tree_digest(args.root), indent=2))
        return 0
    if args.command == "validate-record":
        record = json.loads(args.record.read_text(encoding="utf-8"))
        errors = validate_record(args.kind, record)
        print(json.dumps({"valid": not errors, "errors": errors}, indent=2))
        return 0 if not errors else 1
    if args.command == "scan-placeholders":
        findings = scan_placeholders(args.root)
        print(json.dumps({"count": len(findings), "findings": findings}, indent=2))
        return 0 if not findings else 1
    if args.command == "sandbox-command":
        command = args.task_command
        if command and command[0] == "--":
            command = command[1:]
        import subprocess

        completed = subprocess.run(
            sandbox_command(
                args.repository_root,
                args.writable_root,
                args.working_directory,
                command,
                network=args.network,
            ),
            check=False,
        )
        return completed.returncode
    raise AssertionError("unreachable")


if __name__ == "__main__":
    raise SystemExit(main())
