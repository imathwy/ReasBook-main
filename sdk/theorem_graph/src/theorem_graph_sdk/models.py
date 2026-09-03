"""Typed transport-neutral models for theorem graph generation."""

from __future__ import annotations

from dataclasses import dataclass
from pathlib import Path
from typing import Any, Mapping


@dataclass(frozen=True)
class Project:
    """One book or paper source project."""

    kind: str
    kind_dir: str
    leaf: str
    project_id: str
    root: Path
    root_module: str | None = None

    @property
    def slug(self) -> str:
        return self.project_id.lower()

    @property
    def source_root(self) -> str:
        return f"ReasBook/{self.kind_dir}/{self.project_id}/"


@dataclass
class Candidate:
    """A literature-labelled declaration before representative selection."""

    label: str
    item_id: str
    item_type: str
    number: str
    title: str
    statement: str
    declaration: str
    declaration_kind: str
    module_name: str
    relative_file: str
    line: int
    section_id: str
    section_label: str
    score: float


@dataclass(frozen=True)
class GenerationReport:
    """Summary returned by :class:`GraphGenerator`."""

    project_count: int
    generated_count: int
    skipped_count: int
    output_root: Path
    entries: tuple[dict[str, Any], ...] = ()

    def public_dict(self) -> dict[str, Any]:
        """Return a JSON-friendly generation summary."""

        return {
            "project_count": self.project_count,
            "generated_count": self.generated_count,
            "skipped_count": self.skipped_count,
            "output_root": str(self.output_root),
            "entries": list(self.entries),
        }


def object_value(value: Any, *names: str, default: Any = None) -> Any:
    """Read a field from a mapping or a decoder object."""

    if isinstance(value, Mapping):
        for name in names:
            if name in value:
                return value[name]
        return default
    for name in names:
        if hasattr(value, name):
            return getattr(value, name)
    return default


__all__ = ["Candidate", "GenerationReport", "Project", "object_value"]
