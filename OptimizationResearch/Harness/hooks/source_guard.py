"""Compare safe source snapshots before and after a task."""

from __future__ import annotations

import json
import sys
from pathlib import Path

from optimization_harness.snapshot import tree_digest


def main() -> int:
    if len(sys.argv) != 3:
        raise SystemExit("usage: source_guard.py BEFORE.json SOURCE_ROOT")
    before = json.loads(Path(sys.argv[1]).read_text(encoding="utf-8"))
    after = tree_digest(Path(sys.argv[2]))
    print(json.dumps({"unchanged": before == after, "before": before, "after": after}, indent=2))
    return 0 if before == after else 1


if __name__ == "__main__":
    raise SystemExit(main())
