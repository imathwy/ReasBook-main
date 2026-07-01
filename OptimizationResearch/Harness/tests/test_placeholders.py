from pathlib import Path

from optimization_harness.placeholders import scan_placeholders


def test_placeholder_scan(tmp_path: Path) -> None:
    (tmp_path / "Good.lean").write_text("theorem good : True := by trivial\n", encoding="utf-8")
    assert scan_placeholders(tmp_path) == []
    (tmp_path / "Bad.lean").write_text("theorem bad : True := by sorry\n", encoding="utf-8")
    assert scan_placeholders(tmp_path)[0]["file"] == "Bad.lean"
