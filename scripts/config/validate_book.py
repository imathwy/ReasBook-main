#!/usr/bin/env python3
"""Validate a book.yml against the public schema (read-only, unprivileged).

Usage:
    python3 scripts/config/validate_book.py ReasBook/Books/<BookId>/book.yml [--toolchain <path>]

Checks:
  * YAML parses and conforms to config/schemas/book.schema.json;
  * `id` matches the directory name (Title_AuthorLastName_Year);
  * `branch` matches the version recorded in the branch's ReasBook/lean-toolchain
    (pass --toolchain ReasBook/lean-toolchain to enable this check);
  * `toolchain` in book.yml equals the lean-toolchain content.

Exit code 0 on success, 1 on failure.
"""
from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path

def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("book_yml", help="path to book.yml")
    parser.add_argument("--toolchain", help="path to the branch's ReasBook/lean-toolchain (optional)")
    args = parser.parse_args()
    try:
        import yaml
        from jsonschema import Draft202012Validator
    except ModuleNotFoundError:
        print(
            "error: book validation dependencies are missing; install "
            "scripts/config/requirements.txt",
            file=sys.stderr,
        )
        return 2

    root = Path(__file__).resolve().parents[2]
    schema_path = root / "config" / "schemas" / "book.schema.json"
    book_path = Path(args.book_yml)
    errors = []

    if not book_path.is_file():
        print(f"error: not found: {book_path}")
        return 1

    try:
        data = yaml.safe_load(book_path.read_text(encoding="utf-8"))
    except Exception as exc:  # noqa: BLE001
        print(f"error: cannot parse YAML: {exc}")
        return 1

    schema = json.loads(schema_path.read_text(encoding="utf-8"))
    validator = Draft202012Validator(schema)
    for err in sorted(validator.iter_errors(data), key=lambda e: list(e.path)):
        errors.append(f"schema: {err.message} (at {list(err.path) or 'root'})")

    if isinstance(data, dict):
        # id vs directory name
        dir_name = book_path.parent.name
        if data.get("id") != dir_name:
            errors.append(f"id '{data.get('id')}' does not match directory '{dir_name}'")

        # toolchain / branch consistency
        if args.toolchain:
            tc_path = Path(args.toolchain)
            if tc_path.is_file():
                tc = tc_path.read_text(encoding="utf-8").strip()
                if data.get("toolchain") != tc:
                    errors.append(f"toolchain '{data.get('toolchain')}' != lean-toolchain '{tc}'")
                branch_version = tc.removeprefix("leanprover/lean4:")
                if data.get("branch") != branch_version:
                    errors.append(f"branch '{data.get('branch')}' != lean-toolchain version '{branch_version}'")

    if errors:
        for e in errors:
            print(f"FAIL: {e}")
        return 1

    print(f"OK: {book_path} is valid")
    return 0


if __name__ == "__main__":
    sys.exit(main())
