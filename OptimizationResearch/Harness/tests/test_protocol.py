from optimization_harness.protocol import audit_protocol


def test_complete_protocol_passes() -> None:
    protocol = {
        "protocol_id": "h1-c0-c1",
        "hypothesis": "retrieval improves top-k recall",
        "corpus_version": "optimization-pilot-v0",
        "benchmark_version": "benchmark-v0",
        "baseline": "c0",
        "experiment": "c1",
        "active_variable": ["retrieval"],
        "fixed_variables": ["model", "budget"],
        "metrics": ["top_k_recall"],
        "success_criteria": ["higher top_k_recall"],
        "invalid_run_rules": ["config drift"],
        "stopping_rules": ["all fixed tasks complete"],
        "negative_result_policy": "retain",
    }
    assert audit_protocol(protocol) == []


def test_multiple_active_variables_are_rejected() -> None:
    protocol = {
        "active_variable": ["retrieval", "verifier"],
        "negative_result_policy": "discard",
    }
    findings = audit_protocol(protocol)
    assert "a component comparison must have exactly one active variable" in findings
    assert "negative results must be retained" in findings
