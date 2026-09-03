from __future__ import annotations

import tempfile
import unittest
from unittest.mock import patch
from pathlib import Path

from reasbook_build_sdk import CommandResult, ProjectDocumentationBuilder
from reasbook_build_sdk import docs as docs_module


class _DocsRunner:
    def __init__(self, modules: tuple[str, ...]) -> None:
        self.modules = modules
        self.commands = []

    def run(self, command):
        self.commands.append(command)
        argv = command.argv
        build = Path(argv[argv.index("--build") + 1])
        if "single" in argv:
            if "api-docs.db" in argv:
                (build / "api-docs.db").write_text("database", encoding="utf-8")
        elif "fromDb" in argv or "index" in argv:
            doc = build / "doc"
            doc.mkdir(parents=True, exist_ok=True)
            (doc / "style.css").write_text("body{}", encoding="utf-8")
            (doc / "index.html").write_text(
                "<!doctype html><html><body>documentation index</body></html>\n",
                encoding="utf-8",
            )
            for module in self.modules:
                page = doc / Path(*module.split(".")).with_suffix(".html")
                page.parent.mkdir(parents=True, exist_ok=True)
                page.write_text(
                    "<!doctype html><html><body><h1>Project API</h1>"
                    '<a href="../../Mathlib/Dependency.html">dependency</a>'
                    "<p>This page is deliberately long enough to pass validation.</p>"
                    "</body></html>\n",
                    encoding="utf-8",
                )
        return CommandResult(command=command, returncode=0)


class ProjectDocumentationTests(unittest.TestCase):
    def _project(self, root: Path, *, modern: bool) -> Path:
        project = root / "ReasBook"
        project.mkdir()
        (project / "lakefile.lean").write_text(
            "package ReasBook where\n", encoding="utf-8"
        )
        (project / "lean-toolchain").write_text(
            "leanprover/lean4:v4.30.0\n", encoding="utf-8"
        )
        module = project / "Books" / "Demo" / "Book.lean"
        module.parent.mkdir(parents=True)
        module.write_text("import Mathlib\n", encoding="utf-8")
        package = project / ".lake" / "packages" / "doc-gen4"
        executable = package / ".lake" / "build" / "bin" / "doc-gen4"
        executable.parent.mkdir(parents=True)
        executable.write_text("fixture", encoding="utf-8")
        executable.chmod(0o755)
        (package / "Main.lean").write_text(
            "def fromDb := ()\n" if modern else "def index := ()\n",
            encoding="utf-8",
        )
        return project

    def test_modern_builder_closes_links_and_reuses_exact_cache(self) -> None:
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            project = self._project(root, modern=True)
            modules = ("Books.Demo.Book",)
            runner = _DocsRunner(modules)
            builder = ProjectDocumentationBuilder(runner=runner)
            output = root / "cache" / "docs"
            result = builder.build(
                project,
                modules,
                output,
                repository="https://github.com/acme/reasbook",
                revision="a" * 40,
            )
            self.assertFalse(result.reused)
            self.assertEqual(result.mode, "database")
            self.assertEqual(result.dependency_stubs, 1)
            stub = output / "doc" / "Mathlib" / "Dependency.html"
            self.assertIn("data-reasbook-doc-stub", stub.read_text(encoding="utf-8"))
            command_count = len(runner.commands)

            cached = builder.build(
                project,
                modules,
                output,
                repository="https://github.com/acme/reasbook",
                revision="a" * 40,
            )
            self.assertTrue(cached.reused)
            self.assertEqual(len(runner.commands), command_count)

    def test_legacy_builder_uses_single_then_index(self) -> None:
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            project = self._project(root, modern=False)
            modules = ("Books.Demo.Book",)
            runner = _DocsRunner(modules)
            result = ProjectDocumentationBuilder(runner=runner).build(
                project,
                modules,
                root / "cache" / "docs",
            )
            self.assertEqual(result.mode, "legacy")
            verbs = [
                "single" if "single" in command.argv else "index"
                for command in runner.commands
            ]
            self.assertEqual(verbs, ["single", "index"])

    def test_publish_failure_restores_previous_docs(self) -> None:
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            project = self._project(root, modern=False)
            output = root / "cache" / "docs"
            output.mkdir(parents=True)
            (output / "sentinel.txt").write_text("previous", encoding="utf-8")
            real_replace = docs_module.os.replace
            calls = 0

            def fail_publication(source, destination):
                nonlocal calls
                calls += 1
                if calls == 2:
                    raise OSError("simulated publication failure")
                return real_replace(source, destination)

            with patch(
                "reasbook_build_sdk.docs.os.replace",
                side_effect=fail_publication,
            ):
                with self.assertRaises(OSError):
                    ProjectDocumentationBuilder(
                        runner=_DocsRunner(("Books.Demo.Book",))
                    ).build(
                        project,
                        ("Books.Demo.Book",),
                        output,
                    )

            self.assertEqual(
                (output / "sentinel.txt").read_text(encoding="utf-8"),
                "previous",
            )
            self.assertEqual(list(output.parent.glob(".docs.backup-*")), [])


if __name__ == "__main__":
    unittest.main()
