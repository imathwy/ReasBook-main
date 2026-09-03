"""Pure declaration parsing and dependency contraction algorithms."""

from __future__ import annotations

import json
import re
from pathlib import Path
from typing import Any, Iterable

from .errors import GraphConfigError
from .models import Candidate, Project


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

PALETTE = (
    ("#315fb5", "#e9effa"),
    ("#23745d", "#e4f2ed"),
    ("#a14d3d", "#f8eae6"),
    ("#9a6a12", "#fbf1d8"),
    ("#7654a6", "#eee8f8"),
    ("#28768a", "#e2f1f4"),
)


def natural_key(value: str) -> tuple[tuple[int, object], ...]:
    """Return a total ordering key that handles mixed numeric/text pieces."""

    return tuple(
        (0, int(part)) if part.isdigit() else (1, part.lower())
        for part in NATURAL_PART_RE.split(value)
        if part
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
    value = re.sub(r"\s+", " ", value).strip(' :%-."')
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
        try:
            for line in readme.read_text(encoding="utf-8").splitlines():
                if line.startswith("# "):
                    return line[2:].strip()
        except OSError:
            pass
    return project.project_id.replace("_", " ")


def _module_parts(module: str) -> list[str]:
    parts: list[str] = []
    current: list[str] = []
    quoted = False
    for char in module:
        if char == "«":
            quoted = True
        elif char == "»":
            quoted = False
        if char == "." and not quoted:
            parts.append("".join(current))
            current = []
        else:
            current.append(char)
    parts.append("".join(current))
    return [part.replace("«", "").replace("»", "") for part in parts if part]


def module_relative_file(project: Project, module_name: str) -> str:
    parts = _module_parts(module_name)
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
    expected_tail = "/".join(suffix).lower() + ".lean"
    try:
        files = list(project.root.rglob(f"{suffix[-1]}.lean"))
    except OSError:
        files = []
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
    normalized_stem = re.sub(r"[^a-z0-9]", "", Path(relative_file).stem.lower())
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
    if item_type in {
        "Theorem",
        "Lemma",
        "Proposition",
        "Corollary",
    } and declaration_kind in {
        "theorem",
        "opaque",
    }:
        score += 30
    score += min(line, 100000) / 1_000_000
    return score


def candidates_from_raw(
    project: Project, declarations: Iterable[dict[str, Any]]
) -> list[Candidate]:
    candidates: list[Candidate] = []
    for declaration in declarations:
        doc = str(declaration.get("docString") or "").strip()
        match = LABEL_RE.match(doc)
        if not match:
            continue
        label, item_id, item_type = normalize_label(
            match.group("kind"), match.group("number")
        )
        number = match.group("number").replace("_", ".").replace("-", ".")
        module_name = str(declaration.get("moduleName") or "")
        relative_file = module_relative_file(project, module_name)
        try:
            line = int(declaration.get("line") or 1)
        except (TypeError, ValueError):
            line = 1
        section_id, section_label = section_for(relative_file, number)
        declaration_kind = str(declaration.get("kind") or "")
        candidates.append(
            Candidate(
                label=label,
                item_id=item_id,
                item_type=item_type,
                number=number,
                title=title_from_doc(doc, match, label),
                statement=doc,
                declaration=str(declaration.get("name") or ""),
                declaration_kind=declaration_kind,
                module_name=module_name,
                relative_file=relative_file,
                line=line,
                section_id=section_id,
                section_label=section_label,
                score=candidate_score(
                    label, item_type, doc, declaration_kind, relative_file, line
                ),
            )
        )
    return candidates


def fallback_raw_declarations(project: Project) -> list[dict[str, Any]]:
    """Extract labelled declarations from source when no compiled env exists."""

    declarations: list[dict[str, Any]] = []
    for file in sorted(project.root.rglob("*.lean"), key=lambda path: path.as_posix()):
        try:
            text = file.read_text(encoding="utf-8", errors="replace")
        except OSError:
            continue
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
    selected = [
        max(
            group,
            key=lambda item: (
                item.score,
                -item.line,
                item.relative_file,
                item.declaration,
            ),
        )
        for group in groups.values()
    ]
    selected.sort(
        key=lambda item: natural_key(
            f"{item.relative_file}:{item.line:08d}:{item.label}"
        )
    )
    return selected


def contract_dependencies(
    declaration: str,
    raw_by_name: dict[str, dict[str, Any]],
    selected_by_name: dict[str, str],
) -> list[str]:
    """Contract helper declarations until the nearest selected items."""

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
    try:
        data = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError) as exc:
        raise GraphConfigError(f"invalid theorem-map manifest {path}: {exc}") from exc
    if not isinstance(data, dict) or not isinstance(data.get("items"), list):
        raise GraphConfigError(f"invalid theorem-map manifest: {path}")
    return data


def build_data(
    project: Project,
    raw_declarations: list[dict[str, Any]],
    repository: str,
    branch: str,
    commit: str,
) -> dict[str, Any]:
    """Build the stable JSON payload consumed by the graph frontend."""

    curated = load_curated_manifest(project)
    if curated is not None:
        data = dict(curated)
        data.setdefault("schemaVersion", 1)
        project_data = dict(data.get("project") or {})
        project_data.update(
            {
                "id": project.project_id,
                "title": project_data.get("title") or project_title(project),
                "kind": project.kind,
                "branch": branch,
                "commit": commit,
                "repository": repository.rstrip("/"),
                "sourceRoot": project.source_root,
            }
        )
        data["project"] = project_data
        return data

    candidates = candidates_from_raw(project, raw_declarations)
    selected = select_representatives(candidates)
    raw_by_name = {
        str(item.get("name")): item for item in raw_declarations if item.get("name")
    }
    selected_by_name = {item.declaration: item.item_id for item in selected}
    items: list[dict[str, Any]] = []
    for candidate in selected:
        dependencies = contract_dependencies(
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
            "repository": repository.rstrip("/"),
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


__all__ = [
    "CHAPTER_RE",
    "DECL_RE",
    "LABEL_RE",
    "Candidate",
    "PALETTE",
    "build_data",
    "candidate_score",
    "candidates_from_raw",
    "clean_title_text",
    "contract_dependencies",
    "fallback_raw_declarations",
    "load_curated_manifest",
    "module_relative_file",
    "natural_key",
    "normalize_label",
    "project_title",
    "section_for",
    "select_representatives",
    "slugify",
    "title_from_doc",
]
