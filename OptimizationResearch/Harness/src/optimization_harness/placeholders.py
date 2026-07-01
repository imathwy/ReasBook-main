"""Lean placeholder scanner."""

from __future__ import annotations

import re
from pathlib import Path

PATTERN = re.compile(r"\b(sorry|admit)\b")


def scan_placeholders(root: Path) -> list[dict[str, object]]:
    findings: list[dict[str, object]] = []
    for path in sorted(root.rglob("*.lean")):
        for line_number, line in enumerate(path.read_text(encoding="utf-8").splitlines(), 1):
            if PATTERN.search(line):
                findings.append(
                    {
                        "file": path.relative_to(root).as_posix(),
                        "line": line_number,
                        "text": line.strip(),
                    }
                )
    return findings
