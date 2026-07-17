"""Canonical book/paper paths, module prefixes, targets, and entry generation."""

from __future__ import annotations

from dataclasses import dataclass
import json
from pathlib import Path


@dataclass(frozen=True)
class ProjectSpec:
    kind: str
    name: str
    directory: Path
    entry_name: str
    module_prefix: str
    target: str

    @property
    def entry(self) -> Path:
        return self.directory / self.entry_name

    @property
    def key(self) -> str:
        return f"{self.kind}:{self.name}"


def resolve(project_root: Path, kind: str, name: str) -> ProjectSpec:
    if kind == "book":
        return ProjectSpec(
            kind="book", name=name,
            directory=project_root / "Books" / name,
            entry_name="Book.lean", module_prefix=name,
            target=f"{name}.Book",
        )
    if kind == "paper":
        return ProjectSpec(
            kind="paper", name=name,
            directory=project_root / "Papers" / name,
            entry_name="Paper.lean", module_prefix=f"Papers.{name}",
            target=f"Papers.{name}.Paper",
        )
    raise ValueError(f"unsupported project kind: {kind}")


def discover(project_root: Path) -> list[ProjectSpec]:
    specs = []
    papers_dir = project_root / "Papers"
    paper_names = {
        path.parent.name for path in papers_dir.glob("*/Paper.lean")
    } if papers_dir.exists() else set()
    books_dir = project_root / "Books"
    if books_dir.exists():
        for path in books_dir.glob("*/Book.lean"):
            if path.parent.name not in paper_names:
                specs.append(resolve(project_root, "book", path.parent.name))
    for name in paper_names:
        specs.append(resolve(project_root, "paper", name))
    return sorted(specs, key=lambda spec: (spec.kind, spec.name))


def module_for(spec: ProjectSpec, source: Path) -> str:
    parts = source.relative_to(spec.directory).with_suffix("").parts
    quoted = [f"«{part}»" if part and part[0].isdigit() else part for part in parts]
    return ".".join((spec.module_prefix, *quoted))


def source_files(spec: ProjectSpec) -> list[Path]:
    return sorted(
        path for path in spec.directory.rglob("*.lean")
        if ".lake" not in path.parts and path.name not in {"Book.lean", "Paper.lean"}
    )


def generate_entry(spec: ProjectSpec) -> int:
    imports = ["import Mathlib", *(f"import {module_for(spec, path)}" for path in source_files(spec))]
    spec.entry.write_text("\n".join(imports) + "\n", encoding="utf-8")
    return len(imports) - 1


def clear_degradation(repo_root: Path, kind: str, name: str) -> bool:
    manifest = repo_root / "scripts" / "state" / "degradations.json"
    if not manifest.exists():
        return False
    data = json.loads(manifest.read_text(encoding="utf-8"))
    entries = data.get("entries")
    if not isinstance(entries, list):
        raise ValueError("scripts/state/degradations.json has no entries list")
    retained = [
        entry for entry in entries
        if not (entry.get("kind") == kind and entry.get("name") == name)
    ]
    if len(retained) == len(entries):
        return False
    data["entries"] = retained
    manifest.write_text(json.dumps(data, indent=2, ensure_ascii=False) + "\n", encoding="utf-8")
    return True
