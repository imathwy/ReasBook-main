from __future__ import annotations

import json
import io
import tempfile
import unittest
from contextlib import redirect_stdout
from pathlib import Path

from theorem_graph_sdk import (
    GraphGenerator,
    GraphRenderError,
    LABEL_RE,
    Project,
    SourceExtractor,
    TheoremGraphConfig,
    build_data,
    contract_dependencies,
    copy_curated_map,
    generic_projects,
    normalize_label,
)
from theorem_graph_sdk.projects import discover_root_module
from theorem_graph_sdk.render import read_catalog_entry, write_catalog


class TheoremGraphSdkTests(unittest.TestCase):
    def test_discover_root_module_accepts_explicit_lake_root(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            compiled = root / "build" / "lib" / "lean"
            compiled.mkdir(parents=True)
            (compiled / "TR_LALM_theory.olean").write_bytes(b"olean")

            self.assertEqual(
                discover_root_module(
                    root,
                    "TR_LALM_theory",
                    "Paper",
                    compiled_root=compiled,
                ),
                "TR_LALM_theory",
            )

    @staticmethod
    def no_projects(*_args, **_kwargs):
        return []

    def test_label_and_dependency_contract(self) -> None:
        self.assertEqual(
            normalize_label("theorem", "A.2_3"),
            ("Theorem A.2.3", "theorem-a-2-3", "Theorem"),
        )
        raw = {
            "Article.main": {"dependencies": ["Internal.bridge"]},
            "Internal.bridge": {"dependencies": ["Article.base", "Mathlib.fact"]},
            "Article.base": {"dependencies": []},
        }
        self.assertEqual(
            contract_dependencies(
                "Article.main",
                raw,
                {"Article.main": "theorem-2-2", "Article.base": "lemma-2-1"},
            ),
            ["lemma-2-1"],
        )

    def test_hyphenated_literature_label(self) -> None:
        match = LABEL_RE.match("Corollary 1-11-21: a subgroup consequence.")
        self.assertIsNotNone(match)
        assert match is not None
        self.assertEqual(match.group("number"), "1-11-21")

    def test_generic_projects_are_opt_in(self) -> None:
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            curated_root = root / "curated"
            generated_root = root / "generated"
            (curated_root / "theorem-map").mkdir(parents=True)
            (curated_root / "theorem-map" / "index.html").write_text(
                "<!doctype html>", encoding="utf-8"
            )
            curated = Project(
                "papers", "Papers", "Paper", "Curated", curated_root
            )
            generated = Project(
                "books", "Books", "Book", "Generated", generated_root
            )
            self.assertEqual(generic_projects([curated, generated], False), [])
            self.assertEqual(
                generic_projects([curated, generated], True), [generated]
            )

    def test_build_data_selects_labelled_declarations(self) -> None:
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            (root / "Section_2.lean").write_text("-- source", encoding="utf-8")
            project = Project("books", "Books", "Book", "Demo", root)
            raw = [
                {
                    "name": "helper",
                    "moduleName": "Demo.Section_2",
                    "line": 2,
                    "kind": "lemma",
                    "docString": "Lemma 2.1 (base result).",
                    "dependencies": [],
                },
                {
                    "name": "main",
                    "moduleName": "Demo.Section_2",
                    "line": 8,
                    "kind": "theorem",
                    "docString": "Theorem 2.2: main result.",
                    "dependencies": ["helper"],
                },
            ]
            data = build_data(
                project,
                raw,
                repository="https://example.invalid/repo",
                branch="v4.32.2",
                commit="abc",
            )
            self.assertEqual(
                [item["id"] for item in data["items"]],
                ["lemma-2-1", "theorem-2-2"],
            )
            self.assertEqual(data["items"][1]["dependencies"], ["lemma-2-1"])

    def test_generator_publishes_curated_and_catalog(self) -> None:
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            source = root / "ReasBook" / "Papers" / "Demo"
            source.mkdir(parents=True)
            (source / "Paper.lean").write_text(
                "-- no generated source", encoding="utf-8"
            )
            curated = source / "theorem-map"
            curated.mkdir()
            (curated / "index.html").write_text("<!doctype html>", encoding="utf-8")
            (curated / "metadata.json").write_text(
                json.dumps(
                    {
                        "project": {
                            "id": "stale",
                            "title": "Demo",
                            "kind": "papers",
                            "branch": "old-branch",
                            "commit": "old-commit",
                            "repository": "https://example.invalid/old",
                            "sourceRoot": "old/root/",
                        },
                        "nodes": 1,
                        "edges": 0,
                    }
                ),
                encoding="utf-8",
            )
            original_app = (
                '(function () {\n'
                '  var LEAN_REF = "old-branch";\n'
                '  var LEAN_COMMIT = "old-commit";\n'
                '  var LEAN_BASE =\n'
                '    "https://example.invalid/old/blob/" +\n'
                '    LEAN_REF + "/old/root/";\n'
                '})();\n'
            )
            (curated / "app.js").write_text(original_app, encoding="utf-8")
            site = root / "site"
            report = GraphGenerator(
                TheoremGraphConfig(
                    repo_root=root,
                    site_root=site,
                    branch="main",
                    commit="abc",
                    repository="https://github.com/optpku/ReasBook.git/",
                ),
                extractor=SourceExtractor(),
                commit_reader=lambda _: "abc",
            ).generate()
            self.assertEqual(report.generated_count, 1)
            self.assertTrue(
                (site / "theorem-maps" / "papers" / "demo" / "index.html").is_file()
            )
            self.assertIn(
                "Demo",
                (site / "theorem-maps" / "index.html").read_text(encoding="utf-8"),
            )
            generated = site / "theorem-maps" / "papers" / "demo"
            metadata = json.loads(
                (generated / "metadata.json").read_text(encoding="utf-8")
            )
            context = json.loads(
                (generated / "release-context.json").read_text(encoding="utf-8")
            )
            expected_identity = {
                "id": "Demo",
                "title": "Demo",
                "kind": "papers",
                "branch": "main",
                "commit": "abc",
                "repository": "https://github.com/optpku/ReasBook",
                "sourceRoot": "ReasBook/Papers/Demo/",
            }
            self.assertEqual(metadata["project"], expected_identity)
            self.assertEqual(context, {"schemaVersion": 1, "project": expected_identity})
            rendered_app = (generated / "app.js").read_text(encoding="utf-8")
            self.assertIn('var LEAN_REF = "main";', rendered_app)
            self.assertIn('var LEAN_COMMIT = "abc";', rendered_app)
            self.assertIn(
                'var LEAN_BASE = "https://github.com/optpku/ReasBook/blob/abc/'
                'ReasBook/Papers/Demo/";',
                rendered_app,
            )
            self.assertEqual(
                (curated / "metadata.json").read_text(encoding="utf-8"),
                json.dumps(
                    {
                        "project": {
                            "id": "stale",
                            "title": "Demo",
                            "kind": "papers",
                            "branch": "old-branch",
                            "commit": "old-commit",
                            "repository": "https://example.invalid/old",
                            "sourceRoot": "old/root/",
                        },
                        "nodes": 1,
                        "edges": 0,
                    }
                ),
            )
            self.assertEqual((curated / "app.js").read_text(encoding="utf-8"), original_app)

    def test_cli_uses_packaged_extractor_and_frontend_resources(self) -> None:
        from theorem_graph_sdk.cli import main

        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            source = root / "ReasBook" / "Books" / "Demo"
            source.mkdir(parents=True)
            (source / "Book.lean").write_text(
                "/-- Theorem 1.1: demo result. -/\n"
                "theorem demo : True := by trivial\n",
                encoding="utf-8",
            )
            site = root / "site"
            output = io.StringIO()
            with redirect_stdout(output):
                code = main(
                    [
                        "--repo-root",
                        str(root),
                        "--site-root",
                        str(site),
                        "--branch",
                        "main",
                        "--commit",
                        "abc",
                        "--include-generic",
                        "--json",
                    ]
                )
            self.assertEqual(code, 0)
            generated = site / "theorem-maps" / "books" / "demo"
            self.assertTrue((generated / "index.html").is_file())
            self.assertTrue((generated / "app.js").is_file())
            self.assertTrue((generated / "styles.css").is_file())
            self.assertTrue((generated / "release-context.json").is_file())
            rendered_app = (generated / "app.js").read_text(encoding="utf-8")
            self.assertIn("encodeURIComponent(project.commit)", rendered_app)
            self.assertNotIn("encodeURIComponent(project.branch)", rendered_app)

    def test_curated_release_link_contract_fails_closed(self) -> None:
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            source = root / "source"
            source.mkdir()
            (source / "index.html").write_text("<!doctype html>", encoding="utf-8")
            (source / "app.js").write_text(
                'var LEAN_REF = "main";\n', encoding="utf-8"
            )
            identity = {
                "id": "Demo",
                "kind": "papers",
                "branch": "main",
                "commit": "a" * 40,
                "repository": "https://github.com/example/ReasBook.git",
                "sourceRoot": "ReasBook/Papers/Demo/",
            }

            with self.assertRaisesRegex(GraphRenderError, "invalid release-link contract"):
                copy_curated_map(source, root / "output", project=identity)

    def test_source_only_marks_compiled_root_as_source_fallback(self) -> None:
        """A source-only run must never claim Lean-environment evidence."""

        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            project_root = root / "ReasBook" / "Papers" / "Demo"
            project_root.mkdir(parents=True)
            (project_root / "Paper.lean").write_text(
                "/-- Theorem 1.1: source result. -/\n"
                "theorem source_result : True := by trivial\n",
                encoding="utf-8",
            )
            project = Project(
                "papers",
                "Papers",
                "Paper",
                "Demo",
                project_root,
                root_module="Demo.Paper",
            )
            report = GraphGenerator(
                TheoremGraphConfig(
                    repo_root=root,
                    site_root=root / "site",
                    branch="v4.32.2",
                    include_generic=True,
                    source_only=True,
                ),
                project_discoverer=lambda *_args, **_kwargs: [project],
                commit_reader=lambda _: "abc",
            ).generate()

            self.assertEqual(report.generated_count, 1)
            data = json.loads(
                (
                    root
                    / "site"
                    / "theorem-maps"
                    / "papers"
                    / "demo"
                    / "data.json"
                ).read_text(encoding="utf-8")
            )
            self.assertEqual(data["generation"]["mode"], "source-fallback")

    def test_empty_run_clears_stale_output_in_replace_mode(self) -> None:
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            site = root / "site"
            stale = site / "theorem-maps" / "books" / "old-book"
            stale.mkdir(parents=True)
            (stale / "index.html").write_text("stale", encoding="utf-8")
            (site / "theorem-maps" / "index.html").write_text(
                "old catalog", encoding="utf-8"
            )
            report = GraphGenerator(
                TheoremGraphConfig(
                    repo_root=root,
                    site_root=site,
                    branch="main",
                ),
                project_discoverer=self.no_projects,
                commit_reader=lambda _: "abc",
            ).generate()
            target = site / "theorem-maps"
            self.assertEqual(report.project_count, 0)
            self.assertTrue((target / "index.html").is_file())
            self.assertFalse(stale.exists())
            self.assertNotIn("old catalog", (target / "index.html").read_text())

    def test_generator_filters_explicit_project_keys(self) -> None:
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            for name in ("Keep", "Skip"):
                source = root / "ReasBook" / "Books" / name
                source.mkdir(parents=True)
                (source / "Book.lean").write_text("-- source", encoding="utf-8")
                curated = source / "theorem-map"
                curated.mkdir()
                (curated / "index.html").write_text(
                    "<!doctype html>", encoding="utf-8"
                )
            report = GraphGenerator(
                TheoremGraphConfig(
                    repo_root=root,
                    site_root=root / "site",
                    branch="main",
                    project_keys=("books/Keep",),
                ),
                commit_reader=lambda _: "abc",
            ).generate()
            self.assertEqual(report.project_count, 1)
            self.assertTrue(
                (
                    root
                    / "site"
                    / "theorem-maps"
                    / "books"
                    / "keep"
                    / "index.html"
                ).is_file()
            )
            self.assertFalse(
                (root / "site" / "theorem-maps" / "books" / "skip").exists()
            )

    def test_no_replace_synchronizes_managed_trees_and_keeps_notes(self) -> None:
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            source = root / "ReasBook" / "Papers" / "NewPaper"
            source.mkdir(parents=True)
            (source / "Paper.lean").write_text("-- source", encoding="utf-8")
            curated = source / "theorem-map"
            curated.mkdir()
            (curated / "index.html").write_text("<!doctype html>", encoding="utf-8")
            site = root / "site"
            old_books = site / "theorem-maps" / "books" / "old"
            old_papers = site / "theorem-maps" / "papers" / "old"
            old_books.mkdir(parents=True)
            old_papers.mkdir(parents=True)
            (old_books / "index.html").write_text("old", encoding="utf-8")
            (old_papers / "index.html").write_text("old", encoding="utf-8")
            (site / "theorem-maps" / "notes.txt").write_text(
                "keep me", encoding="utf-8"
            )
            report = GraphGenerator(
                TheoremGraphConfig(
                    repo_root=root,
                    site_root=site,
                    branch="main",
                    replace_output=False,
                ),
                commit_reader=lambda _: "abc",
            ).generate()
            target = site / "theorem-maps"
            self.assertEqual(report.generated_count, 1)
            self.assertFalse(old_books.exists())
            self.assertFalse(old_papers.exists())
            self.assertTrue(
                (target / "papers" / "newpaper" / "index.html").is_file()
            )
            self.assertEqual(
                (target / "notes.txt").read_text(encoding="utf-8"), "keep me"
            )

    def test_failed_generation_leaves_previous_tree_untouched(self) -> None:
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            source = root / "ReasBook" / "Books" / "Generic"
            source.mkdir(parents=True)
            (source / "Book.lean").write_text("-- source", encoding="utf-8")
            site = root / "site"
            old = site / "theorem-maps" / "books" / "old" / "index.html"
            old.parent.mkdir(parents=True)
            old.write_text("preserve", encoding="utf-8")
            with self.assertRaises(GraphRenderError):
                GraphGenerator(
                    TheoremGraphConfig(
                        repo_root=root,
                        site_root=site,
                        branch="main",
                        include_generic=True,
                        assets=root / "missing-assets",
                    ),
                    commit_reader=lambda _: "abc",
                ).generate()
            self.assertEqual(old.read_text(encoding="utf-8"), "preserve")

    def test_malformed_catalog_metadata_is_reported_as_graph_error(self) -> None:
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp) / "map"
            root.mkdir(parents=True)
            (root / "index.html").write_text("ok", encoding="utf-8")
            (root / "metadata.json").write_text(
                json.dumps({"project": "not-an-object", "nodes": "bad"}),
                encoding="utf-8",
            )
            with self.assertRaises(GraphRenderError):
                read_catalog_entry(root, "books")
            with self.assertRaises(GraphRenderError):
                write_catalog(root.parent, [{"kind": "books", "slug": "x", "title": "X", "nodes": "bad", "edges": 0}])

    def test_catalog_command_data_reads_existing_metadata(self) -> None:
        with tempfile.TemporaryDirectory() as temp:
            site_root = Path(temp)
            map_root = site_root / "theorem-maps" / "papers" / "sample"
            map_root.mkdir(parents=True)
            (map_root / "index.html").write_text("<!doctype html>", encoding="utf-8")
            (map_root / "metadata.json").write_text(
                json.dumps(
                    {
                        "project": {
                            "id": "Sample",
                            "title": "Sample paper",
                            "branch": "v4.32.2",
                        },
                        "nodes": 7,
                        "edges": 9,
                    }
                ),
                encoding="utf-8",
            )
            output = write_catalog(site_root)
            rendered = output.read_text(encoding="utf-8")
            self.assertIn("Sample paper", rendered)
            self.assertIn("v4.32.2", rendered)
            self.assertIn("<td>7</td><td>9</td>", rendered)


if __name__ == "__main__":
    unittest.main()
