"""Deterministic, single-project three-way tree planning and application."""

from __future__ import annotations

import hashlib
import difflib
import os
import shutil
import subprocess
import tempfile
from pathlib import Path, PurePosixPath
from typing import Any, Callable


def _hash(content: bytes | None) -> str | None:
    return hashlib.sha256(content).hexdigest() if content is not None else None


def read_tree(root: Path) -> dict[str, bytes]:
    """Read a directory as a stable relative-path to bytes mapping."""
    if not root.is_dir():
        raise ValueError(f"tree does not exist: {root}")
    result: dict[str, bytes] = {}
    for path in sorted(item for item in root.rglob("*") if item.is_file()):
        relative_path = path.relative_to(root)
        if ".lake" in relative_path.parts:
            continue
        relative = relative_path.as_posix()
        result[relative] = path.read_bytes()
    return result


def tree_hash(tree_or_root: dict[str, bytes] | Path) -> str:
    tree = read_tree(tree_or_root) if isinstance(tree_or_root, Path) else tree_or_root
    digest = hashlib.sha256()
    for path, content in sorted(tree.items()):
        encoded = path.encode("utf-8")
        digest.update(len(encoded).to_bytes(8, "big"))
        digest.update(encoded)
        digest.update(len(content).to_bytes(8, "big"))
        digest.update(content)
    return digest.hexdigest()


def write_tree(tree: dict[str, bytes], destination: Path) -> None:
    if destination.exists():
        shutil.rmtree(destination)
    destination.mkdir(parents=True)
    for relative, content in sorted(tree.items()):
        pure = PurePosixPath(relative)
        if pure.is_absolute() or ".." in pure.parts:
            raise ValueError(f"unsafe tree path: {relative}")
        path = destination.joinpath(*pure.parts)
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_bytes(content)


def render_tree_diff(old_root: Path, new_root: Path, old_label: str, new_label: str) -> str:
    """Render a stable review diff without embedding temporary absolute paths."""
    old = read_tree(old_root)
    new = read_tree(new_root)
    chunks: list[str] = []
    for path in sorted(set(old) | set(new)):
        before = old.get(path)
        after = new.get(path)
        if before == after:
            continue
        if before is not None and after is not None and b"\0" in before + after:
            chunks.append(
                f"Binary files {old_label}/{path} and {new_label}/{path} differ\n"
            )
            continue
        before_lines = (
            before.decode("utf-8", errors="replace").splitlines(keepends=True)
            if before is not None else []
        )
        after_lines = (
            after.decode("utf-8", errors="replace").splitlines(keepends=True)
            if after is not None else []
        )
        chunks.extend(difflib.unified_diff(
            before_lines, after_lines,
            fromfile=f"{old_label}/{path}" if before is not None else "/dev/null",
            tofile=f"{new_label}/{path}" if after is not None else "/dev/null",
        ))
    return "".join(chunks)


def _exact_renames(base: dict[str, bytes], theirs: dict[str, bytes]) -> dict[str, str]:
    """Detect unambiguous exact-content upstream renames."""
    deleted = {path: content for path, content in base.items() if path not in theirs}
    added = {path: content for path, content in theirs.items() if path not in base}
    by_hash: dict[str, list[str]] = {}
    for path, content in added.items():
        by_hash.setdefault(_hash(content) or "", []).append(path)
    renames: dict[str, str] = {}
    for old, content in deleted.items():
        candidates = by_hash.get(_hash(content) or "", [])
        if len(candidates) == 1:
            new = candidates[0]
            if new not in renames.values():
                renames[old] = new
    return renames


def _merge_text(ours: bytes, base: bytes, theirs: bytes) -> tuple[bytes | None, str | None]:
    if b"\0" in ours + base + theirs:
        return None, "binary files changed on both sides"
    with tempfile.TemporaryDirectory() as temporary:
        root = Path(temporary)
        paths = [root / name for name in ("ours", "base", "theirs")]
        for path, content in zip(paths, (ours, base, theirs), strict=True):
            path.write_bytes(content)
        result = subprocess.run(
            ["git", "merge-file", "-p", *map(str, paths)],
            stdout=subprocess.PIPE, stderr=subprocess.PIPE, check=False,
        )
    if result.returncode == 0:
        return result.stdout, None
    if result.returncode == 1:
        return None, "overlapping text changes"
    return None, result.stderr.decode("utf-8", errors="replace").strip() or "git merge-file failed"


def plan_tree_merge(base_root: Path, ours_root: Path, theirs_root: Path, merged_root: Path) -> dict[str, Any]:
    """Plan and stage one complete project tree without modifying ``ours``."""
    base = read_tree(base_root)
    ours = read_tree(ours_root)
    theirs = read_tree(theirs_root)
    renames = _exact_renames(base, theirs)

    virtual_base = dict(base)
    virtual_ours = dict(ours)
    rename_metadata: dict[str, str] = {}
    for old, new in sorted(renames.items()):
        if old in ours and new not in ours:
            virtual_base[new] = base[old]
            virtual_ours[new] = ours[old]
            virtual_base.pop(old, None)
            virtual_ours.pop(old, None)
            rename_metadata[new] = old

    merged: dict[str, bytes] = {}
    entries: list[dict[str, Any]] = []
    conflicts: list[dict[str, Any]] = []
    for path in sorted(set(virtual_base) | set(virtual_ours) | set(theirs)):
        base_content = virtual_base.get(path)
        ours_content = virtual_ours.get(path)
        theirs_content = theirs.get(path)
        entry = {
            "path": path,
            "rename_from": rename_metadata.get(path),
            "base_sha256": _hash(base_content),
            "ours_sha256": _hash(ours_content),
            "theirs_sha256": _hash(theirs_content),
        }
        chosen: bytes | None
        if ours_content == theirs_content:
            chosen = ours_content
            classification = "unchanged" if ours_content == base_content else "identical-change"
        elif ours_content == base_content:
            chosen = theirs_content
            classification = "upstream-delete" if theirs_content is None else "upstream-only"
        elif theirs_content == base_content:
            chosen = ours_content
            classification = "local-delete" if ours_content is None else "local-only"
        elif base_content is not None and ours_content is not None and theirs_content is not None:
            chosen, error = _merge_text(ours_content, base_content, theirs_content)
            classification = "auto-merged" if error is None else "conflict"
            if error:
                entry.update({"conflict_type": "modify/modify", "reason": error})
        else:
            chosen = None
            classification = "conflict"
            if base_content is not None and theirs_content is None and ours_content is not None:
                conflict_type = "rename/modify" if path in renames else "delete/modify"
            elif base_content is not None and ours_content is None and theirs_content is not None:
                conflict_type = "modify/delete"
            else:
                conflict_type = "add/add"
            entry.update({"conflict_type": conflict_type, "reason": "non-mergeable tree change"})
        if entry["rename_from"] and classification == "local-only":
            classification = "rename/local-modify"
        entry["classification"] = classification
        if classification == "conflict":
            entry["resolution"] = "unresolved"
            conflicts.append(dict(entry))
        elif chosen is not None:
            merged[path] = chosen
        entries.append(entry)

    write_tree(merged, merged_root)
    return {
        "base_tree_sha256": tree_hash(base),
        "ours_tree_sha256": tree_hash(ours),
        "theirs_tree_sha256": tree_hash(theirs),
        "merged_tree_sha256": tree_hash(merged),
        "entries": entries,
        "conflicts": conflicts,
        "exact_renames": renames,
    }


def apply_staged_tree(
    staged: Path, target: Path, *,
    post_apply: Callable[[], None] | None = None,
    inject_failure_after_backup: bool = False,
) -> None:
    """Replace one project tree transactionally, restoring it on failure."""
    if not staged.is_dir() or not target.is_dir():
        raise ValueError("staged and target trees must both exist")
    parent = target.parent
    temporary = Path(tempfile.mkdtemp(prefix=f".{target.name}.sync-", dir=parent))
    replacement = temporary / target.name
    backup = parent / f".{target.name}.sync-backup-{os.getpid()}"
    if backup.exists():
        raise ValueError(f"stale synchronization backup exists: {backup}")
    shutil.copytree(staged, replacement)
    moved_original = False
    try:
        target.rename(backup)
        moved_original = True
        if inject_failure_after_backup:
            raise RuntimeError("injected apply failure")
        replacement.rename(target)
        if post_apply is not None:
            post_apply()
        shutil.rmtree(backup)
        moved_original = False
    except Exception:
        if target.exists() and moved_original:
            shutil.rmtree(target)
        if moved_original and backup.exists():
            backup.rename(target)
        raise
    finally:
        shutil.rmtree(temporary, ignore_errors=True)
