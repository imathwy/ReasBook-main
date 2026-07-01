"""Bubblewrap command construction for source-read-only task execution."""

from __future__ import annotations

import shutil
from pathlib import Path


def sandbox_command(
    repository_root: Path,
    writable_root: Path,
    working_directory: Path,
    command: list[str],
    *,
    network: bool = False,
) -> list[str]:
    if not command:
        raise ValueError("command must not be empty")
    bwrap = shutil.which("bwrap")
    if bwrap is None:
        raise RuntimeError("bubblewrap is required for enforced write isolation")
    repository_root = repository_root.resolve(strict=True)
    writable_root = writable_root.resolve(strict=True)
    working_directory = working_directory.resolve(strict=True)
    if not writable_root.is_relative_to(repository_root):
        raise ValueError("writable root must be inside repository")
    if not working_directory.is_relative_to(repository_root):
        raise ValueError("working directory must be inside repository")
    args = [
        bwrap,
        "--die-with-parent",
        "--new-session",
        "--ro-bind",
        "/",
        "/",
        "--bind",
        str(writable_root),
        str(writable_root),
        "--dev-bind",
        "/dev",
        "/dev",
        "--proc",
        "/proc",
        "--tmpfs",
        "/tmp",
        "--chdir",
        str(working_directory),
    ]
    if not network:
        args.append("--unshare-net")
    return [*args, "--", *command]
