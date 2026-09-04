from __future__ import annotations

from contextlib import contextmanager
from contextlib import redirect_stdout
import io
import json
import os
from pathlib import Path
import shutil
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
import update_readme  # noqa: E402
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
    @staticmethod
    def _project_docs_fixture(root: Path) -> tuple[Path, Path, Path, Path]:
        repo = root / "repo"
        scripts = repo / "scripts" / "build"
        build_bin = repo / "sdk" / "build" / "bin"
        deploy_bin = repo / "sdk" / "deploy" / "bin"
        lean_root = repo / "ReasBook"
        for directory in (scripts, build_bin, deploy_bin, lean_root):
            directory.mkdir(parents=True, exist_ok=True)
        for name in ("common.sh", "project_docs.sh"):
            shutil.copy2(ROOT / "scripts" / "build" / name, scripts / name)
        (lean_root / "lakefile.lean").write_text(
            'require doc-gen4 from git "https://example.invalid/doc-gen4"\n',
            encoding="utf-8",
        )
        deploy = deploy_bin / "reasbook-deploy"
        deploy.write_text(
            "#!/usr/bin/env bash\n"
            "set -eu\n"
            'while [ "$#" -gt 0 ] && [ "$1" != -- ]; do shift; done\n'
            '[ "$#" -gt 0 ] || exit 2\n'
            "shift\n"
            'exec "$@"\n',
            encoding="utf-8",
        )
        deploy.chmod(0o755)
        return repo, scripts, lean_root, build_bin / "reasbook-build"

    def test_project_docs_honors_and_validates_release_target_boundary(self) -> None:
        with tempfile.TemporaryDirectory() as temp:
            repo, scripts, lean_root, build_sdk = self._project_docs_fixture(
                Path(temp)
            )
            build_sdk.write_text(
                "#!/usr/bin/env bash\n"
                "set -eu\n"
                'if [ "${1:-}" = targets ]; then\n'
                '  : > "$DISCOVERY_LOG"\n'
                "  printf '%s\\n' Included.Book Excluded.Book\n"
                "  exit 0\n"
                "fi\n"
                "printf '%s\\n' \"$@\" > \"$INVOCATION_LOG\"\n",
                encoding="utf-8",
            )
            build_sdk.chmod(0o755)

            invocation = Path(temp) / "invocation.log"
            discovery = Path(temp) / "discovery.log"
            result = subprocess.run(
                ["bash", str(scripts / "project_docs.sh")],
                cwd=repo,
                env={
                    **os.environ,
                    "REASBOOK_LEAN_ROOT": str(lean_root),
                    "REASBOOK_LAKE_TARGETS": "Included.Book,Second.Paper",
                    "PROJECT_DOC_MODULES": "Excluded.Book",
                    "INVOCATION_LOG": str(invocation),
                    "DISCOVERY_LOG": str(discovery),
                },
                capture_output=True,
                text=True,
                check=False,
            )

            self.assertEqual(result.returncode, 0, result.stderr)
            self.assertIn("2 project root(s)", result.stdout)
            self.assertFalse(discovery.exists())
            arguments = invocation.read_text(encoding="utf-8").splitlines()
            self.assertEqual(
                arguments[:4],
                [
                    "project-docs",
                    str(lean_root),
                    "Included.Book",
                    "Second.Paper",
                ],
            )
            self.assertNotIn("Excluded.Book", arguments)

            empty_result = subprocess.run(
                ["bash", str(scripts / "project_docs.sh")],
                cwd=repo,
                env={
                    **os.environ,
                    "REASBOOK_LEAN_ROOT": str(lean_root),
                    "REASBOOK_LAKE_TARGETS": " , ",
                    "DISCOVERY_LOG": str(discovery),
                },
                capture_output=True,
                text=True,
                check=False,
            )

            self.assertEqual(empty_result.returncode, 2)
            self.assertIn("contains no documentation roots", empty_result.stderr)
            self.assertFalse(discovery.exists())

    def test_readme_resource_labels_describe_release_state(self) -> None:
        english = (ROOT / "README.md").read_text(encoding="utf-8")
        chinese = (ROOT / "README.zh-CN.md").read_text(encoding="utf-8")
        self.assertIn("[简体中文](README.zh-CN.md)", english)
        self.assertIn("[English](README.md)", chinese)

        excluded = {
            "kind": "books",
            "name": "ProbabilityTheory_Klenke_2020",
            "slug": "probabilitytheory_klenke_2020",
        }
        no_verso = {
            "kind": "books",
            "name": "IntegerProgramming_Conforti_2014",
            "slug": "integerprogramming_conforti_2014",
        }

        self.assertEqual(
            update_readme.resource_cell(excluded),
            "Source only (excluded from the current release profile)",
        )
        resource = update_readme.resource_cell(no_verso)
        self.assertIn("Verso not published", resource)
        self.assertNotIn("TBD", resource)
        self.assertEqual(
            update_readme.resource_cell(excluded, language="zh-CN"),
            "仅源代码（不包含在当前发布配置中）",
        )
        chinese_resource = update_readme.resource_cell(no_verso, language="zh-CN")
        self.assertIn("尚未发布 Verso", chinese_resource)
        self.assertNotIn("TBD", chinese_resource)

    def test_verso_build_validates_literate_cache_before_prebuilt_mode(self) -> None:
        script = (ROOT / "scripts" / "build" / "verso.sh").read_text(
            encoding="utf-8"
        )
        generated = script.index('"${generator_args[@]}"')
        cached = script.index(
            'reasbook_run_runtime "$REASBOOK_LEAN_ROOT" "$LITERATE_SDK"'
        )
        enabled = script.index("export REASBOOK_LITERATE_PREBUILT=1")
        built = script.index('reasbook_run_runtime "$REASBOOK_WEB_ROOT"')
        self.assertLess(generated, cached)
        self.assertLess(cached, enabled)
        self.assertLess(enabled, built)
        self.assertIn('export VERSO_GENERATOR=""', script)
        self.assertIn(
            "export VERSO_ENV_REASBOOK_LITERATE_PREBUILT=1", script
        )

    def test_verso_literate_failure_stops_before_web_build(self) -> None:
        source_scripts = ROOT / "scripts" / "build"
        with tempfile.TemporaryDirectory() as temp:
            repo = Path(temp) / "repo"
            scripts = repo / "scripts" / "build"
            for directory in (
                scripts,
                repo / "sdk/common/bin",
                repo / "sdk/deploy/bin",
                repo / "sdk/verso/bin",
                repo / "ReasBook",
                repo / "ReasBookWeb",
            ):
                directory.mkdir(parents=True, exist_ok=True)
            shutil.copy2(source_scripts / "common.sh", scripts / "common.sh")
            shutil.copy2(source_scripts / "verso.sh", scripts / "verso.sh")
            (repo / "sdk/common/bin/python").symlink_to(sys.executable)
            generator = repo / "generator.py"
            generator.write_text(
                "from pathlib import Path\n"
                "Path('ReasBookWeb/.literate-modules.json').write_text("
                "'{\"schema_version\":1,\"modules\":[\"Demo\"]}\\n')\n",
                encoding="utf-8",
            )
            deploy = repo / "sdk/deploy/bin/reasbook-deploy"
            deploy.write_text(
                "#!/usr/bin/env bash\n"
                "set -euo pipefail\n"
                "while [[ $# -gt 0 && $1 != -- ]]; do shift; done\n"
                "shift\n"
                "export REASBOOK_BUILD_LAKE_BIN=/runtime/lake\n"
                "exec \"$@\"\n",
                encoding="utf-8",
            )
            deploy.chmod(0o755)
            literate = repo / "sdk/verso/bin/verso-literate"
            literate.write_text(
                "#!/usr/bin/env bash\n"
                "test \"${REASBOOK_BUILD_LAKE_BIN:-}\" = /runtime/lake\n"
                "exit 17\n",
                encoding="utf-8",
            )
            literate.chmod(0o755)
            web_marker = repo / "web-build-ran"
            web = repo / "sdk/verso/bin/verso-build"
            web.write_text(
                f"#!/usr/bin/env bash\ntouch {web_marker}\n",
                encoding="utf-8",
            )
            web.chmod(0o755)

            result = subprocess.run(
                ["bash", str(scripts / "verso.sh")],
                cwd=repo,
                env={
                    **os.environ,
                    "REASBOOK_REPO_ROOT": str(repo),
                    "REASBOOK_LEAN_ROOT": str(repo / "ReasBook"),
                    "REASBOOK_WEB_ROOT": str(repo / "ReasBookWeb"),
                    "REASBOOK_VERSO_GENERATOR": str(generator),
                },
                capture_output=True,
                text=True,
                check=False,
            )

            self.assertEqual(result.returncode, 17, result.stderr)
            self.assertFalse(web_marker.exists())

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
            literate_manifest = json.loads(
                (web_root / ".literate-modules.json").read_text(encoding="utf-8")
            )
            self.assertEqual(literate_manifest["schema_version"], 1)
            self.assertEqual(
                (web_root / ".literate-modules.json").stat().st_mode & 0o777,
                0o644,
            )
            self.assertEqual(
                literate_manifest["modules"],
                ["Books.DemoBook.Book", "Books.DemoBook.Chap01"],
            )
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

    def test_pages_verifier_accepts_single_page_verso_project(self) -> None:
        project = {
            "kind": "papers",
            "kindTitle": "Papers",
            "name": "DemoPaper",
            "slug": "demopaper",
            "branch": "v4.32.2",
        }
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            site = root / ".site"
            pages = site / "sites" / "demopaper" / "pages"
            project_docs = site / "sites" / "demopaper" / "docs"
            canonical_docs = (
                site / "docs" / "ReasBook" / "Papers" / "DemoPaper"
            )
            (site / "docs" / "ReasBook" / "Books").mkdir(parents=True)
            pages.mkdir(parents=True)
            project_docs.mkdir(parents=True)
            canonical_docs.mkdir(parents=True)
            page = "<!doctype html><html><body>Complete paper</body></html>"
            (site / "index.html").write_text(page, encoding="utf-8")
            (pages / "index.html").write_text(page, encoding="utf-8")
            (project_docs / "Paper.html").write_text(page, encoding="utf-8")
            (canonical_docs / "Paper.html").write_text(page, encoding="utf-8")

            output = io.StringIO()
            values = {
                "PROJECTS_JSON": json.dumps([project]),
                "REASBOOK_REQUIRE_DOCS": "1",
                "REASBOOK_REQUIRE_THEOREM_MAPS": "0",
                "REASBOOK_SITE_ROOT": "/ReasBook/",
            }
            with (
                working_directory(root),
                patch.dict(os.environ, values, clear=False),
                redirect_stdout(output),
            ):
                verify.main()

            self.assertIn("ReasBook pages verified", output.getvalue())

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
            docs = (
                repo
                / "ReasBook"
                / ".lake"
                / "build"
                / "reasbook-project-docs"
                / "doc"
            )
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
            docs = (
                repo
                / "ReasBook"
                / ".lake"
                / "build"
                / "reasbook-project-docs"
                / "doc"
            )
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
