"""Validate registered Phase 0 records with deterministic schema checks."""

from __future__ import annotations

import json
import sys
from pathlib import Path

from optimization_harness.records import validate_record


def main() -> int:
    if len(sys.argv) != 3:
        raise SystemExit("usage: verify_artifacts.py KIND RECORD.json")
    record = json.loads(Path(sys.argv[2]).read_text(encoding="utf-8"))
    findings = validate_record(sys.argv[1], record)
    print(json.dumps({"valid": not findings, "findings": findings}, indent=2))
    return 0 if not findings else 1


if __name__ == "__main__":
    raise SystemExit(main())
