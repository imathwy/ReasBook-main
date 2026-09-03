"""Project discovery for repositories containing ReasBook books and papers."""

from __future__ import annotations

from pathlib import Path

from .errors import GraphConfigError
from .models import Project


def discover_root_module(
    repo_root: Path,
    project_id: str,
    leaf: str,
    *,
    compiled_root: Path | None = None,
) -> str | None:
    """Find a compiled root module, if its .olean is available."""

    compiled = compiled_root or (
        repo_root / "ReasBook" / ".lake" / "build" / "lib" / "lean"
    )
    if not compiled.is_dir():
        return None
    candidates: list[tuple[int, str]] = []
    # Most projects expose ``<Project>.<Leaf>`` while Lake libraries with an
    # explicit ``roots := #[`<Project>]`` expose ``<Project>.olean``.  Search
    # both names so compiled evidence is retained for either layout.
    filenames = {f"{leaf}.olean", f"{project_id}.olean"}
    for filename in filenames:
        for path in compiled.rglob(filename):
            relative = path.relative_to(compiled).with_suffix("")
            if project_id not in relative.parts:
                # A root file has the project ID as its stem rather than as a
                # separate parent component.
                if relative.parts != (project_id,):
                    continue
            module = ".".join(relative.parts)
            penalty = len(relative.parts)
            if relative.parts == (project_id,):
                penalty -= 30
            elif len(relative.parts) >= 2 and relative.parts[-2:] == (
                project_id,
                leaf,
            ):
                penalty -= 20
            elif relative.parts[-1] == project_id:
                penalty -= 15
            candidates.append((penalty, module))
    if not candidates:
        return None
    return min(candidates)[1]


def discover_projects(
    repo_root: Path,
    *,
    source_root: Path | None = None,
    compiled_root: Path | None = None,
) -> list[Project]:
    """Discover directories containing Book.lean or Paper.lean."""

    repo_root = Path(repo_root).expanduser().resolve()
    source = source_root or (repo_root / "ReasBook")
    source = Path(source).expanduser()
    if not source.is_absolute():
        source = repo_root / source
    source = source.resolve()
    if not source.is_dir():
        raise GraphConfigError(f"ReasBook source root does not exist: {source}")
    projects: list[Project] = []
    for kind, kind_dir, leaf in (
        ("books", "Books", "Book"),
        ("papers", "Papers", "Paper"),
    ):
        parent = source / kind_dir
        if not parent.is_dir():
            continue
        for root in sorted(parent.iterdir(), key=lambda path: path.name.lower()):
            if not root.is_dir() or not (root / f"{leaf}.lean").is_file():
                continue
            projects.append(
                Project(
                    kind=kind,
                    kind_dir=kind_dir,
                    leaf=leaf,
                    project_id=root.name,
                    root=root,
                    root_module=discover_root_module(
                        repo_root, root.name, leaf, compiled_root=compiled_root
                    ),
                )
            )
    return projects


def has_curated_map(project: Project) -> bool:
    return (project.root / "theorem-map" / "index.html").is_file()


def generic_projects(projects: list[Project], include_generic: bool) -> list[Project]:
    """Select projects that need automatic generation."""

    if not include_generic:
        return []
    return [project for project in projects if not has_curated_map(project)]


__all__ = [
    "Project",
    "discover_projects",
    "discover_root_module",
    "generic_projects",
    "has_curated_map",
]
