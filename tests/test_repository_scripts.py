from __future__ import annotations

from contextlib import contextmanager
from contextlib import redirect_stdout
import io
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch


ROOT = Path(__file__).resolve().parents[1]
PAGES = ROOT / "scripts" / "pages"
if str(PAGES) not in sys.path:
    sys.path.insert(0, str(PAGES))

import assemble  # noqa: E402
import verify  # noqa: E402


@contextmanager
def working_directory(path: Path):
    previous = Path.cwd()
    os.chdir(path)
    try:
        yield
    finally:
        os.chdir(previous)


class RepositoryScriptTests(unittest.TestCase):
    def test_catalog_display_names_preserve_bibliographic_structure(self) -> None:
        self.assertEqual(
            assemble.display_name("RiemannSurfaces_Forster_1981"),
            "Riemann Surfaces (Forster, 1981)",
        )
        self.assertEqual(
            assemble.display_name(
                "IntroductiontoRealAnalysisVolumeI_JiriLebl_2025"
            ),
            "Introduction to Real Analysis Volume I (Jiri Lebl, 2025)",
        )
        self.assertEqual(
            assemble.display_name("TR_LALM_theory"),
            "TR-LALM Theory",
        )

    def test_gen_sections_accepts_option_repo_root(self) -> None:
        generator = ROOT / "ReasBookWeb" / "scripts" / "gen_sections.py"
        with tempfile.TemporaryDirectory() as temp:
            repo = Path(temp) / "checkout"
            lean_root = repo / "ReasBook"
            web_root = repo / "ReasBookWeb"
            (lean_root / "Books" / "DemoBook").mkdir(parents=True)
            (lean_root / "Papers").mkdir()
            (web_root / "ReasBookSite").mkdir(parents=True)
            (lean_root / "lakefile.lean").write_text(
                "import Lake\nopen Lake DSL\nlean_lib Books where\n",
                encoding="utf-8",
            )
            (lean_root / "Books" / "DemoBook" / "Book.lean").write_text(
                "import Mathlib\n", encoding="utf-8"
            )
            (lean_root / "Books" / "DemoBook" / "Chap01.lean").write_text(
                "/-!\n"
                "# Chapter 01 -- A Descriptive Demo Chapter Title\n"
                "-/\n",
                encoding="utf-8",
            )

            result = subprocess.run(
                [sys.executable, str(generator), "--repo-root", str(repo)],
                cwd=repo,
                capture_output=True,
                text=True,
                check=False,
            )

            self.assertEqual(result.returncode, 0, result.stderr)
            self.assertTrue(
                (web_root / "ReasBookSite" / "Sections.lean").is_file()
            )
            sections = (
                web_root / "ReasBookSite" / "Sections.lean"
            ).read_text(encoding="utf-8")
            self.assertIn("demobook/chap01/", sections)
            home = (web_root / "ReasBookSite" / "Home.lean").read_text(
                encoding="utf-8"
            )
            self.assertIn("API documentation", home)
            self.assertNotIn("python3 scripts/gen_sections.py", home)

    def test_gen_sections_links_project_docs_by_lake_root(self) -> None:
        generator = ROOT / "ReasBookWeb" / "scripts" / "gen_sections.py"
        layouts = {
            "aggregate": (
                "lean_lib Papers where\n",
                "Papers/DemoTheory/Paper.html",
            ),
            "flat": (
                'lean_lib DemoTheory where\n  srcDir := "Papers"\n',
                "DemoTheory/Paper.html",
            ),
            "explicit-root": (
                'lean_lib DemoTheory where\n'
                '  srcDir := "Papers"\n'
                "  roots := #[`DemoTheory]\n",
                "DemoTheory.html",
            ),
        }
        for name, (declaration, docs_path) in layouts.items():
            with self.subTest(layout=name), tempfile.TemporaryDirectory() as temp:
                repo = Path(temp) / "checkout"
                lean_root = repo / "ReasBook"
                paper_root = lean_root / "Papers" / "DemoTheory"
                web_root = repo / "ReasBookWeb"
                paper_root.mkdir(parents=True)
                (web_root / "ReasBookSite").mkdir(parents=True)
                (lean_root / "Books").mkdir()
                (lean_root / "lakefile.lean").write_text(
                    "import Lake\nopen Lake DSL\n" + declaration,
                    encoding="utf-8",
                )
                (paper_root / "Paper.lean").write_text(
                    "import Mathlib\n",
                    encoding="utf-8",
                )
                if name == "explicit-root":
                    (lean_root / "Papers" / "DemoTheory.lean").write_text(
                        "import DemoTheory.Paper\n",
                        encoding="utf-8",
                    )

                result = subprocess.run(
                    [sys.executable, str(generator), "--repo-root", str(repo)],
                    cwd=repo,
                    env={
                        **os.environ,
                        "REASBOOK_INCLUDE_PROJECTS": "papers/DemoTheory",
                    },
                    capture_output=True,
                    text=True,
                    check=False,
                )

                self.assertEqual(result.returncode, 0, result.stderr)
                page = (
                    web_root
                    / "ReasBookSite"
                    / "WorkPages"
                    / "Papers"
                    / "DemoTheory.lean"
                ).read_text(encoding="utf-8")
                self.assertIn(f"docs/ReasBook/{docs_path}", page)

    def test_pages_assembly_normalizes_docs_and_generates_landing_page(self) -> None:
        project = {
            "kind": "books",
            "kindTitle": "Books",
            "name": "DemoBook",
            "slug": "demobook",
            "branch": "v4.30.0",
        }
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            monolith = root / ".artifacts" / "monolith"
            docs = monolith / "docs" / "ReasBook" / "Books" / "DemoBook"
            version_docs = (
                monolith
                / "versions"
                / "v4.30.0"
                / "docs"
                / "ReasBook"
                / "DemoBook"
            )
            chapter = monolith / "books" / "demobook" / "chapter-1"
            docs.mkdir(parents=True)
            version_docs.mkdir(parents=True)
            chapter.mkdir(parents=True)
            (monolith / "versions" / "index.html").write_text(
                "versions",
                encoding="utf-8",
            )
            (docs / "Book.html").write_text("docs", encoding="utf-8")
            (version_docs / "Book.html").write_text(
                "versioned docs", encoding="utf-8"
            )
            (chapter / "index.html").write_text("chapter", encoding="utf-8")

            values = {"PROJECTS_JSON": json.dumps([project])}
            with working_directory(root), patch.dict(os.environ, values, clear=False):
                assemble.main()
                verify.main()

            site = root / ".site"
            self.assertTrue(
                (site / "sites" / "demobook" / "docs" / "Book.html").is_file()
            )
            self.assertTrue(
                (site / "sites" / "demobook" / "pages" / "index.html").is_file()
            )
            self.assertTrue((site / "docs" / "ReasBook" / "index.html").is_file())
            docs_index = (site / "docs" / "ReasBook" / "index.html").read_text(
                encoding="utf-8"
            )
            self.assertIn('./Books/DemoBook/', docs_index)
            self.assertTrue((site / "static" / "catalog.css").is_file())
            root_page = (site / "index.html").read_text(encoding="utf-8")
            self.assertIn('id="main-content"', root_page)
            self.assertIn("v4.30.0", root_page)
            canonical_doc = (
                site / "docs" / "ReasBook" / "Books" / "DemoBook" / "Book.html"
            ).read_text(encoding="utf-8")
            self.assertIn(
                "versions/v4.30.0/docs/ReasBook/DemoBook/Book.html",
                canonical_doc,
            )
            self.assertNotIn(".artifacts", canonical_doc)

    def test_pages_verifier_rejects_broken_internal_navigation_link(self) -> None:
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            site = root / ".site"
            (site / "docs" / "ReasBook" / "Books").mkdir(parents=True)
            (site / "docs" / "ReasBook" / "Papers").mkdir()
            (site / "index.html").write_text(
                "<!doctype html><html><body>Home</body></html>",
                encoding="utf-8",
            )
            redirect = site / "sites" / "demo" / "docs" / "Paper.html"
            redirect.parent.mkdir(parents=True)
            redirect.write_text(
                '<meta http-equiv="refresh" content="0; url=/ReasBook/missing/">'
                '<a href="/ReasBook/">Home</a>',
                encoding="utf-8",
            )

            values = {
                "PROJECTS_JSON": "[]",
                "REASBOOK_SITE_ROOT": "/ReasBook/",
            }
            output = io.StringIO()
            with (
                working_directory(root),
                patch.dict(os.environ, values, clear=False),
                redirect_stdout(output),
                self.assertRaises(SystemExit) as raised,
            ):
                verify.main()

            self.assertEqual(raised.exception.code, 1)
            self.assertIn("Broken ReasBook links", output.getvalue())

    def test_link_checker_uses_base_without_treating_it_as_navigation(self) -> None:
        with tempfile.TemporaryDirectory() as temp:
            site = Path(temp)
            page = site / "papers" / "demo" / "index.html"
            target = site / "docs" / "index.html"
            page.parent.mkdir(parents=True)
            target.parent.mkdir(parents=True)
            target.write_text(
                "<!doctype html><html><body>Docs</body></html>",
                encoding="utf-8",
            )
            page.write_text(
                '<!doctype html><html><head><base href="/ReasBook/">'
                '</head><body><a href="docs/">Docs</a></body></html>',
                encoding="utf-8",
            )

            with patch.dict(
                os.environ,
                {"REASBOOK_SITE_ROOT": "/ReasBook/"},
                clear=False,
            ):
                self.assertEqual(verify._missing_internal_references(site), [])

    def test_pages_assembly_omits_version_links_without_version_archive(self) -> None:
        project = {
            "kind": "papers",
            "kindTitle": "Papers",
            "name": "DemoPaper",
            "slug": "demopaper",
            "branch": "v4.30.0",
        }
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            monolith = root / ".artifacts" / "monolith"
            docs = monolith / "docs" / "ReasBook" / "DemoPaper"
            pages = monolith / "papers" / "demopaper"
            docs.mkdir(parents=True)
            pages.mkdir(parents=True)
            html_page = "<!doctype html><html><body>content</body></html>"
            (docs / "Paper.html").write_text(html_page, encoding="utf-8")
            (pages / "index.html").write_text(html_page, encoding="utf-8")
            (pages / "section.html").write_text(html_page, encoding="utf-8")

            values = {"PROJECTS_JSON": json.dumps([project])}
            with working_directory(root), patch.dict(os.environ, values, clear=False):
                assemble.main()

            site = root / ".site"
            for page in (
                site / "index.html",
                site / "sites" / "demopaper" / "index.html",
                site / "docs" / "ReasBook" / "index.html",
            ):
                self.assertNotIn(
                    "Version Archive",
                    page.read_text(encoding="utf-8"),
                )

    def test_pages_assembly_normalizes_explicit_root_documentation(self) -> None:
        project = {
            "kind": "papers",
            "kindTitle": "Papers",
            "name": "DemoTheory",
            "slug": "demotheory",
            "branch": "v4.32.2",
        }
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            docs = root / ".artifacts" / "monolith" / "docs" / "ReasBook"
            (docs / "DemoTheory").mkdir(parents=True)
            (docs / "DemoTheory" / "Lemma.html").write_text(
                "lemma", encoding="utf-8"
            )
            (docs / "DemoTheory.html").write_text("paper", encoding="utf-8")

            values = {"PROJECTS_JSON": json.dumps([project])}
            with working_directory(root), patch.dict(os.environ, values, clear=False):
                assemble.main()

            canonical = (
                root
                / ".site"
                / "docs"
                / "ReasBook"
                / "Papers"
                / "DemoTheory"
                / "Paper.html"
            )
            self.assertEqual(canonical.read_text(encoding="utf-8"), "paper")

    def test_pages_assembly_handles_explicit_root_file_without_directory(self) -> None:
        project = {
            "kind": "papers",
            "kindTitle": "Papers",
            "name": "RootOnly",
            "slug": "rootonly",
            "branch": "v4.32.2",
        }
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            docs = root / ".artifacts" / "monolith" / "docs" / "ReasBook"
            docs.mkdir(parents=True)
            (docs / "RootOnly.html").write_text("paper", encoding="utf-8")

            values = {"PROJECTS_JSON": json.dumps([project])}
            with working_directory(root), patch.dict(os.environ, values, clear=False):
                assemble.main()

            canonical = (
                root
                / ".site"
                / "docs"
                / "ReasBook"
                / "Papers"
                / "RootOnly"
                / "Paper.html"
            )
            self.assertEqual(canonical.read_text(encoding="utf-8"), "paper")

    def test_publish_docs_uses_an_external_repository_root(self) -> None:
        with tempfile.TemporaryDirectory() as temp:
            repo = Path(temp) / "checkout"
            docs = repo / "ReasBook" / ".lake" / "build" / "doc"
            site = repo / "ReasBookWeb" / "_site"
            project_docs = docs / "Books" / "DemoBook"
            project_docs.mkdir(parents=True)
            site.mkdir(parents=True)
            (project_docs / "Book.html").write_text("docs", encoding="utf-8")
            (site / "keep.txt").write_text("keep", encoding="utf-8")

            result = subprocess.run(
                [str(ROOT / "scripts" / "build" / "publish_docs.sh")],
                cwd=repo,
                env={**os.environ, "REASBOOK_REPO_ROOT": str(repo)},
                capture_output=True,
                text=True,
                check=False,
            )

            self.assertEqual(result.returncode, 0, result.stderr)
            self.assertTrue(
                (
                    site
                    / "docs"
                    / "ReasBook"
                    / "Books"
                    / "DemoBook"
                    / "Book.html"
                ).is_file()
            )
            self.assertEqual((site / "keep.txt").read_text(encoding="utf-8"), "keep")

    def test_publish_docs_indexes_flat_project_layout(self) -> None:
        with tempfile.TemporaryDirectory() as temp:
            repo = Path(temp) / "checkout"
            docs = repo / "ReasBook" / ".lake" / "build" / "doc"
            site = repo / "ReasBookWeb" / "_site"
            project_docs = docs / "DemoBook"
            project_docs.mkdir(parents=True)
            site.mkdir(parents=True)
            (project_docs / "Book.html").write_text("docs", encoding="utf-8")

            result = subprocess.run(
                [str(ROOT / "scripts" / "build" / "publish_docs.sh")],
                cwd=repo,
                env={
                    **os.environ,
                    "REASBOOK_REPO_ROOT": str(repo),
                    "REASBOOK_INCLUDE_PROJECTS": "books/DemoBook",
                },
                capture_output=True,
                text=True,
                check=False,
            )

            self.assertEqual(result.returncode, 0, result.stderr)
            index = (site / "docs" / "index.html").read_text(encoding="utf-8")
            self.assertIn("./ReasBook/DemoBook/Book.html", index)


if __name__ == "__main__":
    unittest.main()
