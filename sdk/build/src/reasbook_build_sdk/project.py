"""Discovery and inspection of a Lean Lake project."""

from __future__ import annotations

import os
import re
import tomllib
from dataclasses import dataclass
from pathlib import Path
from typing import Iterable

from .errors import ProjectError


_LEAN_PACKAGE = re.compile(r"\bpackage\s+«([^»]+)»")
_LEAN_PACKAGE_ASCII = re.compile(r"\bpackage\s+([A-Za-z_][A-Za-z0-9_]*)")
_LEAN_BUILD_DIR = re.compile(r"\bbuildDir\s*:=\s*\"([^\"]+)\"")


@dataclass(frozen=True)
class LakeProject:
    """Validated project metadata used by all build layers."""

    root: Path
    lakefile: Path
    toolchain_file: Path
    toolchain: str
    package_name: str | None = None

    @property
    def build_roots(self) -> tuple[Path, ...]:
        """Likely output roots, including a configured Lake ``buildDir``."""

        roots: list[Path] = [self.root / ".lake" / "build", self.root / "build"]
        if self.lakefile.suffix == ".toml":
            try:
                text = self.lakefile.read_text(encoding="utf-8")
            except (OSError, UnicodeError):
                text = ""
            try:
                payload = tomllib.loads(text)
            except ValueError:
                payload = {}
            if isinstance(payload, dict):
                containers: Iterable[object] = (payload, payload.get("package"))
                for container in containers:
                    if isinstance(container, dict) and isinstance(
                        container.get("buildDir"), str
                    ):
                        candidate = Path(container["buildDir"])
                        if _safe_relative(candidate):
                            roots.append(self.root / candidate)
        else:
            try:
                text = self.lakefile.read_text(encoding="utf-8")
            except (OSError, UnicodeError):
                text = ""
            for raw in _LEAN_BUILD_DIR.findall(text):
                candidate = Path(raw)
                if _safe_relative(candidate):
                    roots.append(self.root / candidate)
        unique: list[Path] = []
        seen: set[Path] = set()
        for root in roots:
            resolved = root.resolve(strict=False)
            if resolved not in seen:
                seen.add(resolved)
                unique.append(resolved)
        return tuple(unique)


def _safe_relative(path: Path) -> bool:
    return not path.is_absolute() and all(
        part not in {"", ".", ".."} for part in path.parts
    )


def _package_name(lakefile: Path) -> str | None:
    try:
        text = lakefile.read_text(encoding="utf-8")
    except (OSError, UnicodeError):
        return None
    if lakefile.suffix == ".toml":
        try:
            payload = tomllib.loads(text)
        except ValueError:
            payload = {}
        if isinstance(payload, dict):
            package = payload.get("package")
            if isinstance(package, dict) and isinstance(package.get("name"), str):
                return package["name"]
            if isinstance(payload.get("name"), str):
                return payload["name"]
        match = re.search(r"^\s*name\s*=\s*[\"']([^\"']+)[\"']", text, re.MULTILINE)
        return match.group(1) if match else None
    match = _LEAN_PACKAGE.search(text) or _LEAN_PACKAGE_ASCII.search(text)
    return match.group(1) if match else None


def discover_project(project_root: str | Path) -> LakeProject:
    """Validate and return metadata for a Lake project.

    Discovery is intentionally read-only.  It does not run ``lake update`` or
    rewrite manifests, making it safe to call while constructing a review or
    deployment plan.
    """

    root = Path(project_root).expanduser().resolve(strict=False)
    if not root.is_dir():
        raise ProjectError(f"Lean project directory does not exist: {root}")
    lakefile = next(
        (
            candidate
            for candidate in (root / "lakefile.lean", root / "lakefile.toml")
            if candidate.is_file()
        ),
        None,
    )
    if lakefile is None:
        raise ProjectError(f"no lakefile.lean or lakefile.toml found under {root}")
    toolchain_file = root / "lean-toolchain"
    if not toolchain_file.is_file():
        raise ProjectError(f"missing lean-toolchain under {root}")
    try:
        toolchain = toolchain_file.read_text(encoding="utf-8").strip()
    except (OSError, UnicodeError) as exc:
        raise ProjectError(f"cannot read {toolchain_file}: {exc}") from exc
    if not toolchain:
        raise ProjectError(f"lean-toolchain is empty: {toolchain_file}")
    return LakeProject(
        root=root,
        lakefile=lakefile,
        toolchain_file=toolchain_file,
        toolchain=toolchain,
        package_name=_package_name(lakefile),
    )


def first_artifact(
    project: LakeProject, extensions: tuple[str, ...] = (".olean",)
) -> Path | None:
    """Find one project artifact without traversing dependency packages."""

    normalized = tuple(ext if ext.startswith(".") else f".{ext}" for ext in extensions)
    for root in project.build_roots:
        if not root.is_dir():
            continue
        for directory, directories, files in os.walk(root):
            directory_path = Path(directory)
            if directory_path == project.root:
                directories[:] = [
                    name for name in directories if name not in {".git", ".lake"}
                ]
            elif directory_path == root or directory_path in {
                project.root / ".lake",
                project.root / ".lake" / "build",
            }:
                directories[:] = [name for name in directories if name != "packages"]
            for filename in files:
                if filename.endswith(normalized):
                    return directory_path / filename
    return None
