from pathlib import Path

import pytest

from optimization_harness.sandbox import sandbox_command


def test_sandbox_binds_only_isolated_root_writable(tmp_path: Path) -> None:
    repository = tmp_path / "repo"
    writable = repository / "OptimizationResearch"
    repository.mkdir()
    writable.mkdir()
    command = sandbox_command(repository, writable, repository, ["true"])
    writable_index = command.index("--bind")
    assert command[writable_index + 1 : writable_index + 3] == [str(writable), str(writable)]
    assert "--unshare-net" in command


def test_sandbox_rejects_external_writable_root(tmp_path: Path) -> None:
    repository = tmp_path / "repo"
    writable = tmp_path / "elsewhere"
    repository.mkdir()
    writable.mkdir()
    with pytest.raises(ValueError):
        sandbox_command(repository, writable, repository, ["true"])
