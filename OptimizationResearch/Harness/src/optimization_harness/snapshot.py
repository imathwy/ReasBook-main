"""Safe source-tree snapshots used to prove read-only source invariants."""

from __future__ import annotations

import hashlib
from pathlib import Path

SKIP_DIRS = {".git", ".lake", "__pycache__", "Runs", "logs", "outputs", "secrets"}


def _is_secret_like(path: Path) -> bool:
    name = path.name
    return name == ".env" or name.startswith(".env.") or name.endswith((".key", ".pem"))


def tree_digest(root: Path) -> dict[str, object]:
    """Hash non-secret regular files without reading ignored caches or credentials."""
    root = root.resolve(strict=True)
    digest = hashlib.sha256()
    files = 0
    for path in sorted(root.rglob("*")):
        relative = path.relative_to(root)
        if any(part in SKIP_DIRS for part in relative.parts):
            continue
        if not path.is_file() or path.is_symlink() or _is_secret_like(path):
            continue
        digest.update(relative.as_posix().encode())
        digest.update(b"\0")
        digest.update(hashlib.sha256(path.read_bytes()).digest())
        files += 1
    return {"root": root.name, "files": files, "sha256": digest.hexdigest()}
