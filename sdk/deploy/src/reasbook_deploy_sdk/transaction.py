"""Small recoverable transaction for deployment metadata files."""

from __future__ import annotations

import os
from pathlib import Path
import shutil
import tempfile

from .errors import DeployExecutionError


class FileTransaction:
    """Snapshot a bounded set of files and restore them on failure.

    Deployment artifacts are JSON files and are cheap to snapshot. Large Lake
    trees remain outside this transaction; their writes are isolated by cache
    identity and the deployment lock.
    """

    def __init__(self, workspace: str | Path) -> None:
        candidate = Path(workspace).expanduser()
        if any(char in str(candidate) for char in "\x00\r\n"):
            raise DeployExecutionError("transaction workspace contains a control character")
        if candidate.is_symlink():
            raise DeployExecutionError(f"transaction workspace must not be a symlink: {candidate}")
        self._workspace = candidate.resolve()
        self._workspace.mkdir(parents=True, exist_ok=True)
        self._temporary = Path(
            tempfile.mkdtemp(prefix=".deploy-transaction-", dir=self._workspace)
        )
        self._snapshots: dict[Path, Path | None] = {}

    def watch(self, path: str | Path) -> Path:
        candidate = Path(path).expanduser()
        if not candidate.is_absolute():
            candidate = Path.cwd() / candidate
        if candidate.is_symlink():
            raise DeployExecutionError(f"refusing to transact over symlink: {candidate}")
        destination = candidate.resolve(strict=False)
        if destination in self._snapshots:
            return destination
        if destination.is_file():
            backup = self._temporary / str(len(self._snapshots))
            backup.parent.mkdir(parents=True, exist_ok=True)
            shutil.copy2(destination, backup)
            self._snapshots[destination] = backup
        elif destination.exists():
            raise DeployExecutionError(f"deployment artifact is not a regular file: {destination}")
        else:
            self._snapshots[destination] = None
        return destination

    def rollback(self) -> None:
        errors: list[str] = []
        for destination, backup in self._snapshots.items():
            try:
                if destination.is_symlink():
                    destination.unlink()
                if backup is None:
                    destination.unlink(missing_ok=True)
                    continue
                destination.parent.mkdir(parents=True, exist_ok=True)
                os.replace(backup, destination)
            except OSError as exc:
                errors.append(f"{destination}: {exc}")
        self.close()
        if errors:
            raise DeployExecutionError("could not roll back deployment artifacts: " + "; ".join(errors))

    def commit(self) -> None:
        self.close()

    def close(self) -> None:
        shutil.rmtree(self._temporary, ignore_errors=True)

    def __enter__(self) -> "FileTransaction":
        return self

    def __exit__(self, exception_type: object, exception: object, traceback: object) -> None:
        if exception_type is not None:
            self.rollback()
        else:
            self.commit()


__all__ = ["FileTransaction"]
