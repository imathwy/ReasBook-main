"""Validated separation of automation, repair-session, and project states."""

from __future__ import annotations

from typing import Any

RUN_RESULTS = {
    "full-pass", "repair-incomplete", "infrastructure-failure", "manually-degraded",
}
SESSION_STATES = {"active", "checkpointed", "blocked", "completed"}
PROJECT_STATES = {
    "repair-pending", "repair-active", "repair-checkpointed", "repair-blocked", "full-pass",
}

STATE_COMBINATIONS = {
    "full-pass": {("completed", "full-pass")},
    "repair-incomplete": {
        ("active", "repair-active"),
        ("checkpointed", "repair-checkpointed"),
        ("blocked", "repair-blocked"),
    },
    "infrastructure-failure": {
        ("active", "repair-pending"),
        ("checkpointed", "repair-checkpointed"),
        ("blocked", "repair-blocked"),
    },
    "manually-degraded": {
        ("active", "repair-active"),
        ("checkpointed", "repair-checkpointed"),
        ("blocked", "repair-blocked"),
    },
}

CHECKPOINT_FIELDS = {
    "last_checkpoint", "current_root", "next_command", "branch", "commit",
}
BLOCKER_FIELDS = {"condition", "reproduction", "restore_when"}
BUDGET_ONLY_MARKERS = ("8 root", "eight root", "budget reached", "time budget")


def default_states(run_result: str) -> tuple[str, str]:
    """Return a truthful non-terminal default for a run result."""
    if run_result == "full-pass":
        return "completed", "full-pass"
    if run_result == "infrastructure-failure":
        return "active", "repair-pending"
    return "active", "repair-active"


def project_state_for(run_result: str, session_state: str) -> str:
    """Return the unique project state compatible with both inputs."""
    matches = {
        project_state
        for candidate_session, project_state in STATE_COMBINATIONS.get(run_result, set())
        if candidate_session == session_state
    }
    if len(matches) != 1:
        raise ValueError(
            f"no valid project state for run_result={run_result!r}, "
            f"session_state={session_state!r}"
        )
    return matches.pop()


def validate_lifecycle(record: dict[str, Any]) -> list[str]:
    """Return deterministic findings for one lifecycle evidence record."""
    findings: list[str] = []
    run_result = record.get("run_result")
    session_state = record.get("session_state")
    project_state = record.get("project_state")
    if run_result not in RUN_RESULTS:
        findings.append(f"unknown run_result: {run_result!r}")
    if session_state not in SESSION_STATES:
        findings.append(f"unknown session_state: {session_state!r}")
    if project_state not in PROJECT_STATES:
        findings.append(f"unknown project_state: {project_state!r}")
    if findings:
        return findings
    if (session_state, project_state) not in STATE_COMBINATIONS[run_result]:
        findings.append(
            "invalid lifecycle combination: "
            f"{run_result} + {session_state} + {project_state}"
        )

    resume = record.get("resume") or {}
    if session_state == "checkpointed":
        missing = sorted(field for field in CHECKPOINT_FIELDS if not resume.get(field))
        if missing:
            findings.append("checkpointed session missing resume fields: " + ", ".join(missing))

    blocker = record.get("blocker") or {}
    if session_state == "blocked":
        missing = sorted(field for field in BLOCKER_FIELDS if not blocker.get(field))
        if missing:
            findings.append("blocked session missing blocker fields: " + ", ".join(missing))
        attempts = blocker.get("attempts") or []
        only_solution = bool(blocker.get("only_solution"))
        if len(attempts) < 2 and not only_solution:
            findings.append("blocked session requires two independent attempts or only_solution=true")
        reason = " ".join(str(blocker.get(field, "")) for field in ("condition", "reason")).lower()
        if any(marker in reason for marker in BUDGET_ONLY_MARKERS):
            findings.append("budget or repaired-root count is not a hard blocker")

    if session_state != "completed" and project_state == "full-pass":
        findings.append("only a completed session may set project_state=full-pass")
    return findings


def require_valid_lifecycle(record: dict[str, Any]) -> None:
    findings = validate_lifecycle(record)
    if findings:
        raise ValueError("; ".join(findings))
