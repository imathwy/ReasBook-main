"""Merge already-contracted graphs from isolated Lean environments.

Never combine raw declaration dictionaries from incompatible environments:
independent modules may legally reuse global helper names.
"""

from typing import Any

from .analysis import natural_key
from .errors import ExtractionError


def merge_compiled_graphs(
    graphs: list[dict[str, Any]], source_data: dict[str, Any]
) -> dict[str, Any]:
    """Merge literature items after contracting each valid Lean environment.

    Probability v4.30 contains independently compilable modules that reuse
    global helper names and therefore cannot all inhabit one Lean environment.
    Contracting dependencies before this merge prevents one module's helper
    implementation from leaking into another module's dependency paths.
    """

    if not graphs:
        raise ExtractionError("no isolated compiled graphs were produced")
    source_items = source_data.get("items")
    if not isinstance(source_items, list):
        raise ExtractionError("source inventory has no item list")
    source_by_id = {
        str(item["id"]): item
        for item in source_items
        if isinstance(item, dict) and item.get("id")
    }
    by_id: dict[str, list[dict[str, Any]]] = {}
    sections: list[dict[str, Any]] = []
    section_ids: set[str] = set()
    project: dict[str, Any] | None = None
    raw_declaration_count = 0
    for graph in graphs:
        if graph.get("schemaVersion") != 2:
            raise ExtractionError("isolated compiled graph is not schema v2")
        graph_project = graph.get("project")
        if not isinstance(graph_project, dict):
            raise ExtractionError("isolated compiled graph has no project metadata")
        if project is None:
            project = dict(graph_project)
        elif any(
            project.get(field) != graph_project.get(field)
            for field in ("id", "kind", "branch", "commit")
        ):
            raise ExtractionError("isolated compiled graph project mismatch")
        generation = graph.get("generation")
        if isinstance(generation, dict):
            raw_declaration_count += int(generation.get("rawDeclarationCount") or 0)
        graph_sections = graph.get("sections")
        if isinstance(graph_sections, list):
            for section in graph_sections:
                if not isinstance(section, dict) or not section.get("id"):
                    continue
                section_id = str(section["id"])
                if section_id not in section_ids:
                    section_ids.add(section_id)
                    sections.append(dict(section))
        items = graph.get("items")
        if not isinstance(items, list):
            raise ExtractionError("isolated compiled graph has no item list")
        for item in items:
            if not isinstance(item, dict) or not item.get("id"):
                raise ExtractionError("isolated compiled graph has an invalid item")
            by_id.setdefault(str(item["id"]), []).append(dict(item))
    if project is None:
        raise ExtractionError("isolated compiled graphs have no project")

    merged_items: list[dict[str, Any]] = []
    scalar_fields = (
        "id",
        "label",
        "title",
        "type",
        "section",
        "file",
        "line",
        "declaration",
        "statement",
    )
    for item_id in sorted(by_id, key=natural_key):
        candidates = by_id[item_id]
        preferred = source_by_id.get(item_id)
        matching = []
        if preferred is not None:
            matching = [
                item
                for item in candidates
                if item.get("file") == preferred.get("file")
                and item.get("declaration") == preferred.get("declaration")
            ]
        pool = matching or candidates
        pool.sort(
            key=lambda item: (
                str(item.get("file") or ""),
                int(item.get("line") or 1),
                str(item.get("declaration") or ""),
            )
        )
        base = dict(pool[0])
        same_declaration = [
            item
            for item in pool
            if item.get("file") == base.get("file")
            and item.get("declaration") == base.get("declaration")
        ]
        for item in same_declaration:
            if any(item.get(field) != base.get(field) for field in scalar_fields):
                raise ExtractionError(
                    f"inconsistent repeated compiled item metadata: {item_id}"
                )
        statement = {
            str(value)
            for item in same_declaration
            for value in item.get("statementDependencies") or []
        }
        proof = {
            str(value)
            for item in same_declaration
            for value in item.get("proofDependencies") or []
        }
        base["statementDependencies"] = sorted(statement, key=natural_key)
        base["proofDependencies"] = sorted(proof, key=natural_key)
        base["dependencies"] = sorted(statement | proof, key=natural_key)
        base["dependencyEvidence"] = "compiled"
        merged_items.append(base)
    return {
        "schemaVersion": 2,
        "project": project,
        "sections": sections,
        "items": merged_items,
        "generation": {
            "mode": "lean-environment",
            "rootModule": "isolated-adaptive-chunks",
            "rawDeclarationCount": raw_declaration_count,
            "dependencyModel": "statement-and-proof-v1",
            "isolatedEnvironmentCount": len(graphs),
            "compiledCandidateOccurrenceCount": sum(
                len(values) for values in by_id.values()
            ),
        },
    }
