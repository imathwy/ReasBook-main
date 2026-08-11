#!/usr/bin/env python3
"""Generate theorem dependency maps for every ReasBook project on a branch.

The generator reads declaration metadata from compiled Lean environments. It
selects documentation comments that begin with a literature label (for example
``Theorem 2.3``), chooses one representative declaration for each label, and
contracts helper declarations when computing dependencies. Projects may ship a
curated ``theorem-map/`` directory; that directory is copied verbatim instead.
"""

from __future__ import annotations

import argparse
import html
import json
import os
import re
import shutil
import subprocess
import sys
import tempfile
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Iterable


LABEL_RE = re.compile(
    r"^\s*(?P<kind>Assumption|Algorithm|Definition|Lemma|Theorem|"
    r"Proposition|Corollary|Remark|Example|Exercise)\s+"
    r"(?P<number>(?:[A-Z]\.)?\d+(?:[._-]\d+)*|[A-Z](?:\.\d+)+)",
    re.IGNORECASE,
)
DECL_RE = re.compile(
    r"/--(?P<doc>.*?)\-/\s*"
    r"(?:@\[[^\]]*\]\s*)*"
    r"(?:noncomputable\s+|private\s+|protected\s+|public\s+|unsafe\s+)*"
    r"(?P<kind>theorem|lemma|def|abbrev|structure|class|inductive|instance)\s+"
    r"(?P<name>[^\s({:\[=]+)",
    re.DOTALL,
)
NATURAL_PART_RE = re.compile(r"(\d+)")
TITLE_PAREN_RE = re.compile(r"^\s*\(([^)]+)\)")
SECTION_FILE_RE = re.compile(r"^(?:section|sec)[_-]?(\d+)", re.IGNORECASE)
CHAPTER_RE = re.compile(r"^chap(?:ter)?[_-]?(\d+)$", re.IGNORECASE)

PALETTE = [
    ("#315fb5", "#e9effa"),
    ("#23745d", "#e4f2ed"),
    ("#a14d3d", "#f8eae6"),
    ("#9a6a12", "#fbf1d8"),
    ("#7654a6", "#eee8f8"),
    ("#28768a", "#e2f1f4"),
]


@dataclass(frozen=True)
class Project:
    kind: str
    kind_dir: str
    leaf: str
    project_id: str
    root: Path
    root_module: str | None

    @property
    def slug(self) -> str:
        return self.project_id.lower()

    @property
    def source_root(self) -> str:
        return f"ReasBook/{self.kind_dir}/{self.project_id}/"


@dataclass
class Candidate:
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


def natural_key(value: str) -> tuple[Any, ...]:
    return tuple(
        int(part) if part.isdigit() else part.lower()
        for part in NATURAL_PART_RE.split(value)
    )


def slugify(value: str) -> str:
    slug = re.sub(r"[^a-z0-9]+", "-", value.lower()).strip("-")
    return slug or "item"


def normalize_label(kind: str, number: str) -> tuple[str, str, str]:
    canonical_kind = kind[0].upper() + kind[1:].lower()
    canonical_number = number.replace("_", ".")
    label = f"{canonical_kind} {canonical_number}"
    return label, slugify(label), canonical_kind


def clean_title_text(value: str) -> str:
    value = re.sub(r"`([^`]*)`", r"\1", value)
    value = re.sub(r"\[([^]]+)\]\([^)]+\)", r"\1", value)
    value = re.sub(r"\s+", " ", value).strip(" :-.")
    if len(value) > 120:
        value = value[:117].rstrip() + "..."
    return value


def title_from_doc(doc: str, match: re.Match[str], label: str) -> str:
    rest = doc[match.end() :].lstrip()
    parenthetical = TITLE_PAREN_RE.match(rest)
    if parenthetical:
        proposed = clean_title_text(parenthetical.group(1))
        if re.search(r"[A-Za-z]", proposed) and not re.fullmatch(
            r"(?:part\s*)?[ivx\d]+", proposed, re.IGNORECASE
        ):
            return proposed
        rest = rest[parenthetical.end() :].lstrip()
    rest = rest.lstrip(":.- ")
    first = re.split(r"\n\s*\n|(?<=[.!?])\s+", rest, maxsplit=1)[0]
    return clean_title_text(first) or label


def project_title(project: Project) -> str:
    readme = project.root / "README.md"
    if readme.is_file():
        for line in readme.read_text(encoding="utf-8").splitlines():
            if line.startswith("# "):
                return line[2:].strip()
    return project.project_id.replace("_", " ")


def module_relative_file(project: Project, module_name: str) -> str:
    parts = module_name.split(".")
    try:
        index = parts.index(project.project_id)
    except ValueError:
        return ""
    suffix = parts[index + 1 :]
    if not suffix:
        return ""
    candidate = Path(*suffix).with_suffix(".lean")
    if (project.root / candidate).is_file():
        return candidate.as_posix()

    files = list(project.root.rglob(f"{suffix[-1]}.lean"))
    expected_tail = "/".join(suffix).lower() + ".lean"
    for file in files:
        relative = file.relative_to(project.root).as_posix()
        if relative.lower().endswith(expected_tail):
            return relative
    if len(files) == 1:
        return files[0].relative_to(project.root).as_posix()
    return candidate.as_posix()


def section_for(relative_file: str, number: str) -> tuple[str, str]:
    parts = Path(relative_file).parts
    for part in parts:
        chapter = CHAPTER_RE.match(part)
        if chapter:
            value = str(int(chapter.group(1)))
            return f"chapter-{value}", f"Chapter {value}"
    for part in reversed(parts):
        section = SECTION_FILE_RE.match(Path(part).stem)
        if section:
            value = str(int(section.group(1)))
            return f"section-{value}", f"Section {value}"
    first = re.match(r"(?:[A-Z]\.)?(\d+)", number, re.IGNORECASE)
    if first:
        value = str(int(first.group(1)))
        return f"section-{value}", f"Section {value}"
    appendix = re.match(r"([A-Z])\.", number, re.IGNORECASE)
    if appendix:
        value = appendix.group(1).upper()
        return f"appendix-{value.lower()}", f"Appendix {value}"
    return "overview", "Overview"


def candidate_score(
    label: str,
    item_type: str,
    doc: str,
    declaration_kind: str,
    relative_file: str,
    line: int,
) -> float:
    normalized_label = re.sub(r"[^a-z0-9]", "", label.lower())
    normalized_stem = re.sub(
        r"[^a-z0-9]", "", Path(relative_file).stem.lower()
    )
    score = min(len(doc), 6000) / 100.0
    if normalized_stem == normalized_label:
        score += 500
    elif normalized_label in normalized_stem:
        score += 180
    first_paragraph = doc[:500].lower()
    if "source-facing" in first_paragraph:
        score += 120
    if "main statement" in first_paragraph or "main theorem" in first_paragraph:
        score += 60
    if "helper" in first_paragraph or "intermediate" in first_paragraph:
        score -= 100
    if item_type in {"Theorem", "Lemma", "Proposition", "Corollary"} and (
        declaration_kind in {"theorem", "opaque"}
    ):
        score += 30
    score += min(line, 100000) / 1_000_000
    return score


def candidates_from_raw(project: Project, declarations: list[dict[str, Any]]) -> list[Candidate]:
    candidates: list[Candidate] = []
    for declaration in declarations:
        doc = str(declaration.get("docString") or "").strip()
        match = LABEL_RE.match(doc)
        if not match:
            continue
        label, item_id, item_type = normalize_label(
            match.group("kind"), match.group("number")
        )
        number = match.group("number").replace("_", ".")
        module_name = str(declaration.get("moduleName") or "")
        relative_file = module_relative_file(project, module_name)
        line = int(declaration.get("line") or 1)
        section_id, section_label = section_for(relative_file, number)
        candidates.append(
            Candidate(
                label=label,
                item_id=item_id,
                item_type=item_type,
                number=number,
                title=title_from_doc(doc, match, label),
                statement=doc,
                declaration=str(declaration.get("name") or ""),
                declaration_kind=str(declaration.get("kind") or ""),
                module_name=module_name,
                relative_file=relative_file,
                line=line,
                section_id=section_id,
                section_label=section_label,
                score=candidate_score(
                    label,
                    item_type,
                    doc,
                    str(declaration.get("kind") or ""),
                    relative_file,
                    line,
                ),
            )
        )
    return candidates


def fallback_raw_declarations(project: Project) -> list[dict[str, Any]]:
    declarations: list[dict[str, Any]] = []
    for file in sorted(project.root.rglob("*.lean")):
        text = file.read_text(encoding="utf-8")
        relative = file.relative_to(project.root)
        module_suffix = ".".join(relative.with_suffix("").parts)
        module_name = f"{project.project_id}.{module_suffix}"
        for match in DECL_RE.finditer(text):
            line = text.count("\n", 0, match.start()) + 1
            declarations.append(
                {
                    "name": match.group("name"),
                    "moduleName": module_name,
                    "line": line,
                    "kind": match.group("kind"),
                    "docString": match.group("doc").strip(),
                    "dependencies": [],
                }
            )
    return declarations


def select_representatives(candidates: Iterable[Candidate]) -> list[Candidate]:
    groups: dict[str, list[Candidate]] = {}
    for candidate in candidates:
        groups.setdefault(candidate.item_id, []).append(candidate)
    selected = [max(group, key=lambda item: item.score) for group in groups.values()]
    selected.sort(
        key=lambda item: natural_key(f"{item.relative_file}:{item.line:08d}:{item.label}")
    )
    return selected


def nearest_article_dependencies(
    declaration: str,
    raw_by_name: dict[str, dict[str, Any]],
    selected_by_name: dict[str, str],
) -> list[str]:
    result: set[str] = set()
    visited: set[str] = set()
    stack = list(raw_by_name.get(declaration, {}).get("dependencies") or [])
    while stack:
        current = str(stack.pop())
        if current in visited:
            continue
        visited.add(current)
        selected = selected_by_name.get(current)
        if selected:
            result.add(selected)
            continue
        dependency = raw_by_name.get(current)
        if dependency:
            stack.extend(dependency.get("dependencies") or [])
    return sorted(result, key=natural_key)


def load_curated_manifest(project: Project) -> dict[str, Any] | None:
    path = project.root / "theorem-map.json"
    if not path.is_file():
        return None
    data = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(data, dict) or not isinstance(data.get("items"), list):
        raise ValueError(f"Invalid theorem-map manifest: {path}")
    return data


def build_data(
    project: Project,
    raw_declarations: list[dict[str, Any]],
    repository: str,
    branch: str,
    commit: str,
) -> dict[str, Any]:
    curated = load_curated_manifest(project)
    if curated:
        data = dict(curated)
        data.setdefault("schemaVersion", 1)
        data.setdefault("project", {})
        data["project"].update(
            {
                "id": project.project_id,
                "title": data["project"].get("title") or project_title(project),
                "kind": project.kind,
                "branch": branch,
                "commit": commit,
                "repository": repository,
                "sourceRoot": project.source_root,
            }
        )
        return data

    candidates = candidates_from_raw(project, raw_declarations)
    selected = select_representatives(candidates)
    raw_by_name = {
        str(item.get("name")): item
        for item in raw_declarations
        if item.get("name")
    }
    selected_by_name = {item.declaration: item.item_id for item in selected}
    items: list[dict[str, Any]] = []
    for candidate in selected:
        dependencies = nearest_article_dependencies(
            candidate.declaration, raw_by_name, selected_by_name
        )
        dependencies = [item for item in dependencies if item != candidate.item_id]
        items.append(
            {
                "id": candidate.item_id,
                "label": candidate.label,
                "title": candidate.title,
                "type": candidate.item_type,
                "section": candidate.section_id,
                "file": candidate.relative_file,
                "line": candidate.line,
                "declaration": candidate.declaration,
                "statement": candidate.statement,
                "dependencies": dependencies,
            }
        )

    section_ids: list[str] = []
    section_labels: dict[str, str] = {}
    for candidate in selected:
        if candidate.section_id not in section_labels:
            section_ids.append(candidate.section_id)
            section_labels[candidate.section_id] = candidate.section_label
    sections = []
    for index, section_id in enumerate(section_ids):
        color, wash = PALETTE[index % len(PALETTE)]
        sections.append(
            {
                "id": section_id,
                "label": section_labels[section_id],
                "short": section_labels[section_id],
                "color": color,
                "wash": wash,
            }
        )

    return {
        "schemaVersion": 1,
        "project": {
            "id": project.project_id,
            "title": project_title(project),
            "kind": project.kind,
            "branch": branch,
            "commit": commit,
            "repository": repository,
            "sourceRoot": project.source_root,
        },
        "sections": sections,
        "items": items,
        "generation": {
            "mode": "lean-environment" if project.root_module else "source-fallback",
            "rootModule": project.root_module or "",
            "rawDeclarationCount": len(raw_declarations),
        },
    }


def discover_root_module(repo_root: Path, project_id: str, leaf: str) -> str | None:
    compiled = repo_root / "ReasBook" / ".lake" / "build" / "lib" / "lean"
    if not compiled.is_dir():
        return None
    candidates = []
    for path in compiled.rglob(f"{leaf}.olean"):
        relative = path.relative_to(compiled).with_suffix("")
        if project_id not in relative.parts:
            continue
        module = ".".join(relative.parts)
        penalty = len(relative.parts)
        if relative.parts[-2:] == (project_id, leaf):
            penalty -= 10
        candidates.append((penalty, module))
    if not candidates:
        return None
    return min(candidates)[1]


def discover_projects(repo_root: Path) -> list[Project]:
    projects = []
    for kind, kind_dir, leaf in (
        ("books", "Books", "Book"),
        ("papers", "Papers", "Paper"),
    ):
        parent = repo_root / "ReasBook" / kind_dir
        if not parent.is_dir():
            continue
        for root in sorted(parent.iterdir()):
            if not root.is_dir() or not (root / f"{leaf}.lean").is_file():
                continue
            projects.append(
                Project(
                    kind=kind,
                    kind_dir=kind_dir,
                    leaf=leaf,
                    project_id=root.name,
                    root=root,
                    root_module=discover_root_module(repo_root, root.name, leaf),
                )
            )
    return projects


def has_curated_map(project: Project) -> bool:
    return (project.root / "theorem-map" / "index.html").is_file()


def generic_projects(
    projects: Iterable[Project], include_generic: bool
) -> list[Project]:
    if not include_generic:
        return []
    return [project for project in projects if not has_curated_map(project)]


def export_environments(
    repo_root: Path,
    extractor: Path,
    projects: list[Project],
) -> dict[str, list[dict[str, Any]]]:
    exportable = [project for project in projects if project.root_module]
    if not exportable:
        return {}
    config = {
        "projects": [
            {"id": project.project_id, "rootModule": project.root_module}
            for project in exportable
        ]
    }
    print(
        f"[theorem-map] exporting {len(exportable)} compiled project environments",
        flush=True,
    )
    with tempfile.TemporaryDirectory(prefix="reasbook-theorem-map-") as temp:
        temp_root = Path(temp)
        config_path = temp_root / "config.json"
        output_path = temp_root / "raw.json"
        config_path.write_text(json.dumps(config), encoding="utf-8")
        lake = os.environ.get("LAKE_BIN") or shutil.which("lake") or "lake"
        command = [
            lake,
            "env",
            "lean",
            "--run",
            str(extractor.resolve()),
            str(config_path),
            str(output_path),
        ]
        subprocess.run(command, cwd=repo_root / "ReasBook", check=True)
        payload = json.loads(output_path.read_text(encoding="utf-8"))
    return {
        str(project["id"]): list(project.get("declarations") or [])
        for project in payload
    }


def copy_generic_map(
    assets: Path,
    output: Path,
    data: dict[str, Any],
) -> None:
    output.mkdir(parents=True, exist_ok=True)
    for name in ("index.html", "app.js", "styles.css"):
        shutil.copy2(assets / name, output / name)
    (output / "data.json").write_text(
        json.dumps(data, ensure_ascii=False, indent=2) + "\n",
        encoding="utf-8",
    )
    items = list(data.get("items") or [])
    metadata = {
        "schemaVersion": 1,
        "project": data.get("project") or {},
        "nodes": len(items),
        "edges": sum(len(item.get("dependencies") or []) for item in items),
        "generation": data.get("generation") or {},
    }
    (output / "metadata.json").write_text(
        json.dumps(metadata, ensure_ascii=False, indent=2) + "\n",
        encoding="utf-8",
    )


def copy_curated_map(source: Path, output: Path) -> None:
    shutil.copytree(source, output, dirs_exist_ok=True)


def curated_counts(source: Path) -> tuple[int, int]:
    metadata_path = source / "metadata.json"
    if not metadata_path.is_file():
        return 0, 0
    metadata = json.loads(metadata_path.read_text(encoding="utf-8"))
    return int(metadata.get("nodes") or 0), int(metadata.get("edges") or 0)


def write_catalog(site_root: Path, entries: list[tuple[Project, int, int]]) -> None:
    catalog = site_root / "theorem-maps" / "index.html"
    rows = []
    for project, nodes, edges in entries:
        href = f"./{project.kind}/{project.slug}/"
        rows.append(
            "      <tr>"
            f'<td><a href="{html.escape(href)}">{html.escape(project_title(project))}</a></td>'
            f"<td>{html.escape(project.kind[:-1].title())}</td>"
            f"<td>{nodes}</td><td>{edges}</td>"
            "</tr>"
        )
    catalog.parent.mkdir(parents=True, exist_ok=True)
    catalog.write_text(
        "\n".join(
            [
                "<!doctype html>",
                '<html lang="en">',
                "<head>",
                '  <meta charset="utf-8">',
                '  <meta name="viewport" content="width=device-width,initial-scale=1">',
                "  <title>ReasBook Theorem Maps</title>",
                "  <style>",
                "    body{font:16px/1.5 system-ui,sans-serif;max-width:1100px;margin:40px auto;padding:0 20px;color:#1d2833}",
                "    table{width:100%;border-collapse:collapse}th,td{padding:10px 12px;border-bottom:1px solid #d8dee5;text-align:left}",
                "    a{color:#245aa8}th{font-size:13px;text-transform:uppercase;color:#586675}",
                "  </style>",
                "</head>",
                "<body>",
                "  <h1>ReasBook Theorem Maps</h1>",
                "  <p>Literature-level declarations, natural-language statements, and Lean dependencies.</p>",
                "  <table>",
                "    <thead><tr><th>Project</th><th>Kind</th><th>Nodes</th><th>Edges</th></tr></thead>",
                "    <tbody>",
                *rows,
                "    </tbody>",
                "  </table>",
                '  <p><a href="../">Back to ReasBook</a></p>',
                "</body>",
                "</html>",
                "",
            ]
        ),
        encoding="utf-8",
    )


def git_value(repo_root: Path, *args: str) -> str:
    return subprocess.run(
        ["git", *args],
        cwd=repo_root,
        check=True,
        capture_output=True,
        text=True,
    ).stdout.strip()


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repo-root", type=Path, default=Path("."))
    parser.add_argument("--site-root", type=Path, default=Path("ReasBookWeb/_site"))
    parser.add_argument("--branch", required=True)
    parser.add_argument(
        "--repository", default="https://github.com/optpku/ReasBook"
    )
    parser.add_argument(
        "--extractor", type=Path, default=Path(__file__).with_name("Extract.lean")
    )
    parser.add_argument(
        "--assets", type=Path, default=Path(__file__).with_name("assets")
    )
    parser.add_argument(
        "--include-generic",
        action="store_true",
        help="also generate maps from Lean environments for projects without a curated map",
    )
    args = parser.parse_args()

    repo_root = args.repo_root.resolve()
    site_root = (repo_root / args.site_root).resolve()
    extractor = args.extractor.resolve()
    assets = args.assets.resolve()
    projects = discover_projects(repo_root)
    if not projects:
        print("[theorem-map] no ReasBook projects found")
        return 0

    maps_root = site_root / "theorem-maps"
    if maps_root.exists():
        shutil.rmtree(maps_root)

    raw_by_project: dict[str, list[dict[str, Any]]] = {}
    if args.include_generic:
        try:
            automated_projects = generic_projects(projects, args.include_generic)
            raw_by_project = export_environments(
                repo_root, extractor, automated_projects
            )
        except subprocess.CalledProcessError as error:
            print(
                f"[theorem-map] Lean environment export failed ({error}); using source fallback",
                file=sys.stderr,
            )

    commit = git_value(repo_root, "rev-parse", "HEAD")
    entries: list[tuple[Project, int, int]] = []
    for project in projects:
        output = site_root / "theorem-maps" / project.kind / project.slug
        curated_static = project.root / "theorem-map"
        if has_curated_map(project):
            copy_curated_map(curated_static, output)
            item_count, edge_count = curated_counts(curated_static)
            print(f"[theorem-map] {project.project_id}: copied curated static map")
        elif args.include_generic:
            raw = raw_by_project.get(project.project_id)
            if raw is None:
                raw = fallback_raw_declarations(project)
            data = build_data(
                project,
                raw,
                repository=args.repository.rstrip("/"),
                branch=args.branch,
                commit=commit,
            )
            copy_generic_map(assets, output, data)
            item_count = len(data.get("items") or [])
            edge_count = sum(
                len(item.get("dependencies") or []) for item in data.get("items") or []
            )
            print(
                f"[theorem-map] {project.project_id}: {item_count} nodes, {edge_count} edges"
            )
        else:
            print(
                f"[theorem-map] {project.project_id}: skipped (no curated static map)"
            )
            continue
        entries.append((project, item_count, edge_count))

    write_catalog(site_root, entries)
    mode = "curated plus generic" if args.include_generic else "curated only"
    print(f"[theorem-map] generated {len(entries)} project maps ({mode})")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
