from optimization_harness.records import validate_record


def test_valid_project_state() -> None:
    record = {
        "schema_version": "project-state-v0",
        "project_id": "optimization-research",
        "phase": "phase-0",
        "status": "active",
        "active_task": "wp0-preflight",
        "acceptance_criteria": {},
    }
    assert validate_record("project_state", record) == []


def test_missing_field_is_reported() -> None:
    assert "missing required field: task_id" in validate_record(
        "task", {"schema_version": "task-v0"}
    )
