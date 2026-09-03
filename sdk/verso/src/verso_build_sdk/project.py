"""Discovery and validation for a Lake project used by Verso."""

from __future__ import annotations

import re
from dataclasses import dataclass
from pathlib import Path

from .errors import ProjectValidationError


PACKAGE_RE = re.compile(
    r"^[ \t]*package[ \t]+(?:\"([^\"]+)\"|«([^»]+)»|([^ \t]+))(?=\s|$)",
    re.MULTILINE,
)


@dataclass(frozen=True)
class VersoProject:
    """A validated Lake project directory.

    ``lakefile`` may be either the Lean or TOML form.  The SDK deliberately
    does not parse Lake's full DSL; it only needs to establish that the
    project is present and to read the optional toolchain pin.
    """

    root: Path
    lakefile: Path
    toolchain_file: Path | None
    package_name: str | None
    toolchain: str | None


def _read_toolchain(path: Path) -> str:
    try:
        value = path.read_text(encoding="utf-8").strip()
    except OSError as exc:
        raise ProjectValidationError(f"cannot read {path}: {exc}") from exc
    if not value or any(char in value for char in "\x00\r\n"):
        raise ProjectValidationError(
            f"{path} must contain one non-empty toolchain line"
        )
    return value


def discover_project(root: Path, *, require_toolchain: bool = False) -> VersoProject:
    """Validate and describe a Verso/Lake project.

    A toolchain is optional for projects that intentionally use the ambient
    Lake executable.  Set ``require_toolchain`` for reproducible deployments.
    """

    root = Path(root).expanduser().resolve()
    if not root.is_dir():
        raise ProjectValidationError(f"Verso project directory does not exist: {root}")
    lakefile = next(
        (
            candidate
            for candidate in (root / "lakefile.lean", root / "lakefile.toml")
            if candidate.is_file()
        ),
        None,
    )
    if lakefile is None:
        raise ProjectValidationError(
            f"{root} has neither lakefile.lean nor lakefile.toml"
        )
    toolchain_file = root / "lean-toolchain"
    if not toolchain_file.is_file():
        if require_toolchain:
            raise ProjectValidationError(f"missing lean-toolchain in {root}")
        toolchain_file = None
    toolchain = _read_toolchain(toolchain_file) if toolchain_file else None
    package_name: str | None = None
    try:
        lake_text = lakefile.read_text(encoding="utf-8", errors="replace")
    except OSError as exc:
        raise ProjectValidationError(f"cannot read {lakefile}: {exc}") from exc
    match = PACKAGE_RE.search(lake_text)
    if match:
        package_name = next(value for value in match.groups() if value is not None)
    return VersoProject(root, lakefile, toolchain_file, package_name, toolchain)


__all__ = ["VersoProject", "discover_project"]
