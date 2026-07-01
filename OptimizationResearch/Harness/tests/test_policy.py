from pathlib import Path

from optimization_harness.policy import WritePolicy, decide_action


def test_allows_path_inside_isolated_root(tmp_path: Path) -> None:
    writable = tmp_path / "OptimizationResearch"
    writable.mkdir()
    policy = WritePolicy(tmp_path, writable)
    assert policy.decide(writable / "Metadata" / "record.json").decision == "allow"


def test_denies_source_project_path(tmp_path: Path) -> None:
    writable = tmp_path / "OptimizationResearch"
    source = tmp_path / "Nesterov"
    writable.mkdir()
    source.mkdir()
    policy = WritePolicy(tmp_path, writable)
    assert policy.decide(source / "Theorem.lean").decision == "deny"


def test_denies_parent_traversal(tmp_path: Path) -> None:
    writable = tmp_path / "OptimizationResearch"
    writable.mkdir()
    policy = WritePolicy(tmp_path, writable)
    assert policy.decide(writable / ".." / "Nesterov" / "Theorem.lean").decision == "deny"


def test_denies_symlink_escape(tmp_path: Path) -> None:
    writable = tmp_path / "OptimizationResearch"
    source = tmp_path / "Nesterov"
    writable.mkdir()
    source.mkdir()
    (writable / "escape").symlink_to(source, target_is_directory=True)
    policy = WritePolicy(tmp_path, writable)
    assert policy.decide(writable / "escape" / "Theorem.lean").decision == "deny"


def test_high_risk_action_requires_approval() -> None:
    assert decide_action("network").decision == "approval-required"
    assert decide_action("network", approved=True).decision == "allow"


def test_secret_action_is_always_denied() -> None:
    assert decide_action("read-secret", approved=True).decision == "deny"


def test_dry_run_is_non_executing() -> None:
    assert decide_action("dry-run").decision == "dry-run-only"
