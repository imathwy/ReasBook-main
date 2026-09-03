"""Path validation and atomic file publication helpers."""

from __future__ import annotations

import json
import os
import tempfile
from pathlib import Path
from typing import Any


def ensure_absolute(path: str | Path, *, field: str = "path") -> Path:
    """Normalize an absolute path and reject control characters."""

    candidate = Path(path).expanduser()
    if not candidate.is_absolute():
        raise ValueError(f"{field} must be an absolute path: {path!s}")
    if any(char in str(candidate) for char in "\x00\r\n"):
        raise ValueError(f"{field} contains a control character")
    return candidate.resolve(strict=False)


def ensure_within(path: str | Path, root: str | Path, *, field: str = "path") -> Path:
    """Resolve a path and require it to be inside ``root`` or equal to it."""

    resolved = ensure_absolute(path, field=field)
    base = ensure_absolute(root, field="root")
    try:
        resolved.relative_to(base)
    except ValueError as exc:
        raise ValueError(f"{field} {resolved} is outside root {base}") from exc
    return resolved


def safe_relative(path: str | Path, *, field: str = "relative path") -> Path:
    """Validate a relative path used for a marker or generated artifact."""

    candidate = Path(path)
    if candidate.is_absolute() or not candidate.parts:
        raise ValueError(f"{field} must be relative")
    if any(part in {"", ".", ".."} for part in candidate.parts):
        raise ValueError(f"{field} contains an unsafe component: {path!s}")
    if any(char in str(candidate) for char in "\x00\r\n"):
        raise ValueError(f"{field} contains a control character")
    return candidate


def _atomic_replace(path: Path, payload: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    descriptor, temporary_name = tempfile.mkstemp(
        prefix=f".{path.name}.", dir=path.parent
    )
    temporary = Path(temporary_name)
    try:
        with os.fdopen(descriptor, "w", encoding="utf-8", newline="") as handle:
            handle.write(payload)
            handle.flush()
            os.fsync(handle.fileno())
        temporary.replace(path)
    except BaseException:
        temporary.unlink(missing_ok=True)
        raise


def atomic_write_text(path: str | Path, text: str) -> Path:
    """Write UTF-8 text through a same-directory atomic replacement."""

    destination = ensure_absolute(path)
    _atomic_replace(destination, text)
    return destination


def atomic_write_json(path: str | Path, value: Any, *, indent: int = 2) -> Path:
    """Serialize JSON deterministically and replace the destination atomically."""

    payload = (
        json.dumps(value, ensure_ascii=False, indent=indent, sort_keys=True) + "\n"
    )
    return atomic_write_text(path, payload)


__all__ = [
    "atomic_write_json",
    "atomic_write_text",
    "ensure_absolute",
    "ensure_within",
    "safe_relative",
]
