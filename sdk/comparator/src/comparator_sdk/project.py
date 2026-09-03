"""Discovery and output validation for Comparator Lake projects."""

from __future__ import annotations

from dataclasses import dataclass
import re
from pathlib import Path

from reasbook_sdk_common import ensure_absolute, ensure_within

from .errors import ComparatorConfigError


@dataclass(frozen=True)
class LakeProject:
    """A validated Lake project root and its metadata files."""

    root: Path
    lakefile: Path
    toolchain_file: Path
    toolchain: str

    @property
    def build_roots(self) -> tuple[Path, ...]:
        """Likely Lake output roots, including a configured ``buildDir``."""

        roots = [self.root / ".lake" / "build", self.root / "build"]
        try:
            text = self.lakefile.read_text(encoding="utf-8", errors="replace")
        except OSError:
            text = ""
        if self.lakefile.suffix == ".toml":
            matches = re.findall(r'^\s*buildDir\s*=\s*["\']([^"\']+)["\']', text, re.MULTILINE)
        else:
            matches = re.findall(r'\bbuildDir\s*:=\s*"([^"]+)"', text)
        for value in matches:
            candidate = Path(value)
            if not candidate.is_absolute() and all(part not in {"", ".", ".."} for part in candidate.parts):
                roots.append(self.root / candidate)
        unique: list[Path] = []
        seen: set[Path] = set()
        for root in roots:
            resolved = root.resolve(strict=False)
            if resolved not in seen:
                seen.add(resolved)
                unique.append(resolved)
        return tuple(unique)


def _read_toolchain(path: Path) -> str:
    try:
        value = path.read_text(encoding="utf-8").strip()
    except OSError as exc:
        raise ComparatorConfigError(
            f"cannot read toolchain file {path}: {exc}"
        ) from exc
    if not value or any(char in value for char in "\x00\r\n"):
        raise ComparatorConfigError(
            f"toolchain file must contain one non-empty line: {path}"
        )
    return value


def discover_project(
    root: str | Path, *, require_toolchain: bool = True
) -> LakeProject:
    """Validate and describe a target Lake project."""

    try:
        project_root = ensure_absolute(root, field="project root")
    except ValueError as exc:
        raise ComparatorConfigError(str(exc)) from exc
    if not project_root.is_dir():
        raise ComparatorConfigError(f"project directory does not exist: {project_root}")
    lakefile = next(
        (
            candidate
            for candidate in (
                project_root / "lakefile.lean",
                project_root / "lakefile.toml",
            )
            if candidate.is_file()
        ),
        None,
    )
    if lakefile is None:
        raise ComparatorConfigError(
            f"project {project_root} has neither lakefile.lean nor lakefile.toml"
        )
    toolchain_file = project_root / "lean-toolchain"
    if not toolchain_file.is_file():
        if require_toolchain:
            raise ComparatorConfigError(f"missing lean-toolchain in {project_root}")
        toolchain = ""
    else:
        toolchain = _read_toolchain(toolchain_file)
    return LakeProject(project_root, lakefile, toolchain_file, toolchain)


def discover_comparator_root(root: str | Path) -> LakeProject:
    """Validate the checkout containing the Comparator executable source."""

    return discover_project(root, require_toolchain=True)


def resolve_config_path(project_root: Path, config_path: str | Path) -> Path:
    """Resolve a JSON path and keep it inside the target project."""

    candidate = Path(config_path).expanduser()
    if not candidate.is_absolute():
        candidate = project_root / candidate
    try:
        resolved = ensure_within(candidate, project_root, field="Comparator config")
    except ValueError as exc:
        raise ComparatorConfigError(str(exc)) from exc
    if not resolved.is_file():
        raise ComparatorConfigError(f"Comparator config does not exist: {resolved}")
    return resolved


def split_module_name(module: str) -> tuple[str, ...]:
    """Split a Lean module name while preserving dots in quoted identifiers."""

    if not isinstance(module, str) or not module.strip():
        raise ComparatorConfigError("module name must be a non-empty string")
    parts: list[str] = []
    current: list[str] = []
    quoted = False
    for char in module.strip():
        if char == "«":
            quoted = True
        elif char == "»":
            quoted = False
        if char == "." and not quoted:
            if not current:
                raise ComparatorConfigError(f"invalid Lean module name: {module!r}")
            parts.append("".join(current))
            current = []
        else:
            current.append(char)
    if quoted or not current:
        raise ComparatorConfigError(f"invalid Lean module name: {module!r}")
    parts.append("".join(current))
    cleaned: list[str] = []
    for part in parts:
        if part.startswith("«") and part.endswith("»"):
            part = part[1:-1]
        if (
            not part
            or part in {".", ".."}
            or "/" in part
            or "\\" in part
            or any(char in part for char in "\x00\r\n")
        ):
            raise ComparatorConfigError(f"invalid Lean module name: {module!r}")
        cleaned.append(part)
    return tuple(cleaned)


def expected_olean(project_root: Path, module: str) -> Path:
    """Return the conventional `.olean` path for a module."""

    project = discover_project(project_root, require_toolchain=False)
    relative = Path("lib") / "lean" / Path(*split_module_name(module)).with_suffix(".olean")
    for root in project.build_roots:
        candidate = root / relative
        if candidate.is_file():
            return candidate
    return project.build_roots[0] / relative


def verify_module_outputs(
    project_root: Path, modules: tuple[str, ...]
) -> tuple[str, ...]:
    """Return module names whose generated `.olean` file is missing."""

    return tuple(
        module
        for module in modules
        if not expected_olean(project_root, module).is_file()
    )


__all__ = [
    "LakeProject",
    "discover_comparator_root",
    "discover_project",
    "expected_olean",
    "resolve_config_path",
    "split_module_name",
    "verify_module_outputs",
]
