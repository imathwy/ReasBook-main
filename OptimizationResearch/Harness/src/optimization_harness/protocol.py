"""Deterministic checks for experiment protocol completeness."""

from __future__ import annotations

from collections.abc import Mapping

REQUIRED_PROTOCOL_FIELDS = (
    "protocol_id",
    "hypothesis",
    "corpus_version",
    "benchmark_version",
    "baseline",
    "experiment",
    "active_variable",
    "fixed_variables",
    "metrics",
    "success_criteria",
    "invalid_run_rules",
    "stopping_rules",
    "negative_result_policy",
)


def audit_protocol(protocol: Mapping[str, object]) -> list[str]:
    findings = [
        f"missing protocol field: {field}"
        for field in REQUIRED_PROTOCOL_FIELDS
        if field not in protocol
    ]
    active = protocol.get("active_variable")
    if isinstance(active, list) and len(active) != 1:
        findings.append("a component comparison must have exactly one active variable")
    if protocol.get("negative_result_policy") != "retain":
        findings.append("negative results must be retained")
    return findings
