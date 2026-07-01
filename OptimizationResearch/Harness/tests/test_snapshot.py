from pathlib import Path

from optimization_harness.snapshot import tree_digest


def test_digest_changes_with_regular_file(tmp_path: Path) -> None:
    (tmp_path / "A.lean").write_text("theorem a : True := by trivial\n", encoding="utf-8")
    before = tree_digest(tmp_path)
    (tmp_path / "A.lean").write_text("theorem b : True := by trivial\n", encoding="utf-8")
    after = tree_digest(tmp_path)
    assert before["sha256"] != after["sha256"]


def test_digest_ignores_secret_like_file(tmp_path: Path) -> None:
    (tmp_path / "A.lean").write_text("theorem a : True := by trivial\n", encoding="utf-8")
    before = tree_digest(tmp_path)
    (tmp_path / ".env").write_text("DO_NOT_READ=this-is-not-inspected\n", encoding="utf-8")
    after = tree_digest(tmp_path)
    assert before == after
