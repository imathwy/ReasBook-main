from __future__ import annotations

import sqlite3
import tempfile
import unittest
from unittest.mock import patch
from pathlib import Path

from reasbook_build_sdk import BuildFailed, CommandResult, ProjectDocumentationBuilder
from reasbook_build_sdk import docs as docs_module


class _DocsRunner:
    def __init__(self) -> None:
        self.modules: list[str] = []
        self.commands = []

    def run(self, command):
        self.commands.append(command)
        argv = command.argv
        if "--run" in argv:
            adapter = Path(argv[argv.index("--run") + 1])
            control = Path(argv[-1])
            if adapter.name == "ProjectDocsDatabase.lean":
                build = Path(argv[-3])
                modules = tuple(control.read_text(encoding="utf-8").splitlines())
                database = build / argv[-2]
                with sqlite3.connect(database) as connection:
                    connection.execute(
                        "CREATE TABLE IF NOT EXISTS modules "
                        "(name TEXT PRIMARY KEY, source_url TEXT)"
                    )
                    connection.executemany(
                        "INSERT INTO modules (name, source_url) VALUES (?, NULL)",
                        ((module,) for module in modules),
                    )
            else:
                build = Path(argv[-2])
                modules = tuple(
                    line.split("\t", 1)[0]
                    for line in control.read_text(encoding="utf-8").splitlines()
                )
            self.modules.extend(modules)
        elif "fromDb" in argv or "index" in argv:
            build = Path(argv[argv.index("--build") + 1])
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
        module.write_text(
            "import Mathlib\nimport Books.Demo.Chapter\n",
            encoding="utf-8",
        )
        (module.parent / "Chapter.lean").write_text(
            "import Mathlib\n",
            encoding="utf-8",
        )
        (module.parent / "Dead.lean").write_text(
            "import Mathlib\n",
            encoding="utf-8",
        )
        package = project / ".lake" / "packages" / "doc-gen4"
        executable = package / ".lake" / "build" / "bin" / "doc-gen4"
        executable.parent.mkdir(parents=True)
        executable.write_text("fixture", encoding="utf-8")
        executable.chmod(0o755)
        (package / "Main.lean").write_text(
            "def fromDb := ()\n" if modern else "def index := ()\n",
            encoding="utf-8",
        )
        md4lean = (
            project
            / ".lake"
            / "packages"
            / "MD4Lean"
            / ".lake"
            / "build"
            / "lib"
            / ("libMD4Lean_MD4Lean.so" if modern else "libMD4Lean.so")
        )
        md4lean.parent.mkdir(parents=True)
        md4lean.write_bytes(b"fixture")
        (md4lean.parent / "libleanmd4c.so").write_bytes(b"fixture")
        if modern:
            sqlite_ffi = (
                project
                / ".lake"
                / "packages"
                / "leansqlite"
                / ".lake"
                / "build"
                / "lib"
                / "lean"
                / "leansqlite_SQLite_FFI.so"
            )
            sqlite_ffi.parent.mkdir(parents=True)
            sqlite_ffi.write_bytes(b"fixture")
            (sqlite_ffi.parent.parent / "libleansqlite.so").write_bytes(b"fixture")
        return project

    def test_modern_builder_closes_links_and_reuses_exact_cache(self) -> None:
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            project = self._project(root, modern=True)
            modules = ("Books.Demo.Book",)
            runner = _DocsRunner()
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
            self.assertEqual(result.targets, modules)
            self.assertEqual(
                tuple(
                    path.relative_to(output / "doc").as_posix() for path in result.pages
                ),
                ("Books/Demo/Book.html", "Books/Demo/Chapter.html"),
            )
            self.assertNotIn("Books.Demo.Dead", runner.modules)
            self.assertEqual(result.dependency_stubs, 1)
            libraries = [
                Path(value.removeprefix("--load-dynlib=")).name
                for value in runner.commands[0].argv
                if value.startswith("--load-dynlib=")
            ]
            self.assertEqual(
                libraries,
                [
                    "libleansqlite.so",
                    "leansqlite_SQLite_FFI.so",
                ],
            )
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

            chapter = project / "Books" / "Demo" / "Chapter.lean"
            chapter.write_text("import Mathlib\n-- changed\n", encoding="utf-8")
            rebuilt = builder.build(
                project,
                modules,
                output,
                repository="https://github.com/acme/reasbook",
                revision="a" * 40,
            )
            self.assertFalse(rebuilt.reused)
            self.assertGreater(len(runner.commands), command_count)

    def test_legacy_builder_uses_bounded_adapter_then_index(self) -> None:
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            project = self._project(root, modern=False)
            modules = ("Books.Demo.Book",)
            runner = _DocsRunner()
            result = ProjectDocumentationBuilder(runner=runner).build(
                project,
                modules,
                root / "cache" / "docs",
            )
            self.assertEqual(result.mode, "legacy")
            verbs = [
                "batch" if "--run" in command.argv else "index"
                for command in runner.commands
            ]
            self.assertEqual(verbs, ["batch", "index"])
            adapter = runner.commands[0].argv
            libraries = [
                value.removeprefix("--load-dynlib=")
                for value in adapter
                if value.startswith("--load-dynlib=")
            ]
            self.assertEqual(
                [Path(value).name for value in libraries],
                ["libleanmd4c.so", "libMD4Lean.so"],
            )

    def test_md4lean_adapter_rejects_ambiguous_aggregate_libraries(self) -> None:
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            project = self._project(root, modern=False)
            library_root = (
                project / ".lake" / "packages" / "MD4Lean" / ".lake" / "build" / "lib"
            )
            (library_root / "libMD4Lean_MD4Lean.so").write_bytes(b"stale fixture")

            with self.assertRaises(BuildFailed):
                ProjectDocumentationBuilder._md4lean_interpreter_args(project)

    def test_flat_layout_discovers_project_namespace(self) -> None:
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            project = self._project(root, modern=True)
            book = project / "Books" / "Demo" / "Book.lean"
            book.write_text("import Demo.Chapter\n", encoding="utf-8")
            runner = _DocsRunner()

            result = ProjectDocumentationBuilder(runner=runner).build(
                project,
                ("Demo.Book",),
                root / "cache" / "docs-flat",
            )

            self.assertEqual(result.targets, ("Demo.Book",))
            self.assertEqual(runner.modules, ["Demo.Book", "Demo.Chapter"])

    def test_large_project_is_split_into_bounded_analyzer_batches(self) -> None:
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            project = self._project(root, modern=True)
            module_root = project / "Books" / "Demo"
            names = [f"Books.Demo.Part{index:03d}" for index in range(130)]
            (module_root / "Book.lean").write_text(
                "\n".join(f"import {name}" for name in names) + "\n",
                encoding="utf-8",
            )
            for index in range(130):
                (module_root / f"Part{index:03d}.lean").write_text(
                    "import Mathlib\n",
                    encoding="utf-8",
                )
            runner = _DocsRunner()

            result = ProjectDocumentationBuilder(runner=runner).build(
                project,
                ("Books.Demo.Book",),
                root / "cache" / "docs-batched",
            )

            adapter_commands = [
                command for command in runner.commands if "--run" in command.argv
            ]
            self.assertEqual(len(result.pages), 131)
            self.assertEqual(len(adapter_commands), 2)

    def test_explicit_root_includes_only_reachable_sibling_modules(self) -> None:
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            project = self._project(root, modern=True)
            papers = project / "Papers"
            papers.mkdir()
            (papers / "Theory.lean").write_text(
                "public import Theory.Current\n",
                encoding="utf-8",
            )
            namespace = papers / "Theory"
            namespace.mkdir()
            (namespace / "Current.lean").write_text(
                "import Mathlib\n",
                encoding="utf-8",
            )
            (namespace / "Unused.lean").write_text(
                "import Mathlib\n",
                encoding="utf-8",
            )
            runner = _DocsRunner()

            result = ProjectDocumentationBuilder(runner=runner).build(
                project,
                ("Theory",),
                root / "cache" / "docs-explicit",
            )

            self.assertEqual(result.targets, ("Theory",))
            self.assertEqual(runner.modules, ["Theory", "Theory.Current"])
            self.assertEqual(len(result.pages), 2)

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
                    ProjectDocumentationBuilder(runner=_DocsRunner()).build(
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
