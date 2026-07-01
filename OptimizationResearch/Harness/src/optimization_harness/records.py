"""Small schema checks for Phase 0 JSON artifacts."""

from __future__ import annotations

from collections.abc import Mapping

REQUIRED: dict[str, tuple[str, ...]] = {
    "project_state": (
        "schema_version",
        "project_id",
        "phase",
        "status",
        "active_task",
        "acceptance_criteria",
    ),
    "task": (
        "schema_version",
        "task_id",
        "phase",
        "work_package",
        "task_type",
        "status",
        "permissions",
        "required_outputs",
        "checks",
    ),
    "run": (
        "schema_version",
        "run_id",
        "task_id",
        "corpus_version",
        "config_version",
        "evidence",
        "decision",
    ),
    "finding": (
        "schema_version",
        "finding_id",
        "severity",
        "category",
        "claim",
        "evidence",
        "blocking",
    ),
    "experiment_audit": (
        "schema_version",
        "audit_id",
        "protocol_id",
        "status",
        "findings",
        "limitations",
    ),
}


def validate_record(kind: str, record: Mapping[str, object]) -> list[str]:
    if kind not in REQUIRED:
        return [f"unknown record kind: {kind}"]
    errors = [f"missing required field: {field}" for field in REQUIRED[kind] if field not in record]
    if record.get("schema_version") in (None, ""):
        errors.append("schema_version must be non-empty")
    return errors
