from __future__ import annotations

import tempfile
import unittest
from pathlib import Path

from reasbook_build_sdk import ProjectError, discover_project, first_artifact


def make_project(root: Path, *, toml: str = "name = 'Demo'\n") -> Path:
    root.mkdir(parents=True, exist_ok=True)
    (root / "lakefile.toml").write_text(toml, encoding="utf-8")
    (root / "lean-toolchain").write_text("leanprover/lean4:v4.30.0\n", encoding="utf-8")
    return root


class ProjectTests(unittest.TestCase):
    def test_discover_reads_package_and_custom_build_directory(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = make_project(
                Path(tmp) / "demo", toml="name = 'Demo'\n[package]\nbuildDir = 'out'\n"
            )
            project = discover_project(root)
            self.assertEqual(project.package_name, "Demo")
            self.assertIn(root / "out", project.build_roots)

    def test_discover_rejects_missing_toolchain(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp) / "demo"
            root.mkdir()
            (root / "lakefile.toml").write_text("name = 'Demo'\n", encoding="utf-8")
            with self.assertRaises(ProjectError):
                discover_project(root)

    def test_first_artifact_only_looks_at_project_outputs(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = make_project(Path(tmp) / "demo")
            (root / ".lake" / "build" / "lib" / "lean").mkdir(parents=True)
            (root / ".lake" / "build" / "lib" / "lean" / "Demo.olean").write_bytes(b"x")
            self.assertEqual(first_artifact(discover_project(root)).name, "Demo.olean")

    def test_first_artifact_ignores_dependency_packages(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = make_project(Path(tmp) / "demo")
            dependency = root / ".lake" / "build" / "packages" / "mathlib"
            dependency.mkdir(parents=True)
            (dependency / "Dependency.olean").write_bytes(b"x")
            self.assertIsNone(first_artifact(discover_project(root)))


if __name__ == "__main__":
    unittest.main()
