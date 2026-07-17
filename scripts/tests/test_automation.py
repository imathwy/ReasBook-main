from __future__ import annotations

import importlib.util
import contextlib
import io
import json
import os
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path

SCRIPTS = Path(__file__).resolve().parents[1]


def load(name: str, file: str):
    spec = importlib.util.spec_from_file_location(name, SCRIPTS / file)
    module = importlib.util.module_from_spec(spec)
    assert spec.loader
    spec.loader.exec_module(module)
    return module


coverage_module = load("verify_import_coverage", "verify_import_coverage.py")
automation_module = load("run_automation", "run_automation.py")
tips_module = load("update_compatibility_tips", "update_compatibility_tips.py")
fix_module = load("fix_errors", "fix_errors.py")
sync_module = load("sync_from_a", "sync_from_a.py")
upgrade_module = load("upgrade_toolchain", "upgrade_toolchain.py")
inventory_module = load("create_baseline_inventory", "create_baseline_inventory.py")
root_allowlist_module = load("verify_root_allowlist", "verify_root_allowlist.py")
project_lifecycle_verifier = load("verify_project_lifecycle", "verify_project_lifecycle.py")
sync_state_verifier = load("verify_sync_state", "verify_sync_state.py")
import lib.project_scope as scope_module
import lib.project_lifecycle as lifecycle_module


class RepositoryFixture(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.root = Path(self.temp.name)
        self.project = self.root / "ReasBook"
        self.book = self.project / "Books" / "Fixture"
        self.book.mkdir(parents=True)
        self.paper = self.project / "Papers" / "PaperFixture"
        self.paper.mkdir(parents=True)
        (self.project / "lean-toolchain").write_text("leanprover/lean4:v4.30.0\n")
        (self.project / "lake-manifest.json").write_text(json.dumps({
            "packages": [{"name": "mathlib", "rev": "fixture-revision"}]
        }))
        docs = self.root / "docs"
        docs.mkdir()
        state = self.root / "scripts" / "state"
        state.mkdir(parents=True)
        (state / "degradations.json").write_text('{"entries": []}\n')
        (self.book / "Bad.lean").write_text("def bad : Nat := 0\n")
        (self.book / "Dependent.lean").write_text("import Fixture.Bad\ndef dependent := bad\n")
        (self.book / "Book.lean").write_text("import Fixture.Bad\nimport Fixture.Dependent\n")
        (self.paper / "Claim.lean").write_text("def paperClaim : Nat := 0\n")
        (self.paper / "Book.lean").write_text("import Mathlib\n")
        (self.paper / "Paper.lean").write_text("import Papers.PaperFixture.Claim\n")
        subprocess.run(["git", "init", "-q"], cwd=self.root, check=True)
        subprocess.run(["git", "config", "user.email", "fixture@example.test"], cwd=self.root, check=True)
        subprocess.run(["git", "config", "user.name", "Fixture"], cwd=self.root, check=True)
        subprocess.run(["git", "add", "."], cwd=self.root, check=True)
        subprocess.run(["git", "commit", "-qm", "fixture"], cwd=self.root, check=True)
        self.bin = self.root / "bin"
        self.bin.mkdir()

    def tearDown(self):
        self.temp.cleanup()

    def lake(self, body: str):
        path = self.bin / "lake"
        path.write_text("#!/bin/sh\n" + body)
        path.chmod(0o755)

    def env(self):
        env = os.environ.copy()
        env["REASBOOK_ROOT"] = str(self.root)
        env["PATH"] = f"{self.bin}:{env['PATH']}"
        env["PYTHONDONTWRITEBYTECODE"] = "1"
        return env

    def command(self, script: str, *args: str):
        return subprocess.run(
            [sys.executable, str(SCRIPTS / script), *args], cwd=self.root,
            env=self.env(), text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
            check=False,
        )


class CoverageTests(unittest.TestCase):
    def test_lifecycle_separates_run_session_and_project_states(self):
        valid = {
            "run_result": "repair-incomplete",
            "session_state": "checkpointed",
            "project_state": "repair-checkpointed",
            "resume": {
                "last_checkpoint": "run-7", "current_root": "Book.Module",
                "next_command": "lake build Book.Module", "branch": "repair/book",
                "commit": "01234567",
            },
        }
        self.assertEqual(lifecycle_module.validate_lifecycle(valid), [])
        invalid = dict(valid, session_state="completed")
        self.assertIn("invalid lifecycle combination", " ".join(
            lifecycle_module.validate_lifecycle(invalid)
        ))

    def test_lifecycle_rejects_budget_as_blocker(self):
        record = {
            "run_result": "repair-incomplete",
            "session_state": "blocked",
            "project_state": "repair-blocked",
            "blocker": {
                "condition": "budget reached after 8 roots",
                "attempts": ["one", "two"], "reproduction": "lake build X",
                "restore_when": "API exists",
            },
        }
        self.assertIn("not a hard blocker", " ".join(
            lifecycle_module.validate_lifecycle(record)
        ))

    def test_lifecycle_requires_checkpoint_resume_evidence(self):
        record = {
            "run_result": "repair-incomplete",
            "session_state": "checkpointed",
            "project_state": "repair-checkpointed",
        }
        self.assertIn("missing resume fields", " ".join(
            lifecycle_module.validate_lifecycle(record)
        ))

    def test_baseline_status_counts_group_by_path_and_state(self):
        self.assertEqual(
            inventory_module.status_counts([
                " M ReasBook/A.lean", " D ReasBook/B.lean", "?? docs/new.md",
            ]),
            {"ReasBook": {" D": 1, " M": 1}, "docs": {"??": 1}},
        )

    def test_root_allowlist_uses_canonical_paper_target(self):
        old_project = root_allowlist_module.PROJECT
        with tempfile.TemporaryDirectory() as temporary:
            project = Path(temporary)
            book = project / "Books" / "BookFixture"
            paper = project / "Papers" / "PaperFixture"
            book.mkdir(parents=True)
            paper.mkdir(parents=True)
            (book / "Book.lean").write_text("import Mathlib\n")
            (paper / "Paper.lean").write_text("import Mathlib\n")
            root_allowlist_module.PROJECT = project
            try:
                lines = root_allowlist_module.expected_lines({"projects": [
                    {"project": "book:BookFixture", "status": "full-pass", "run_id": "book-run"},
                    {"project": "paper:PaperFixture", "status": "repair-incomplete", "run_id": "paper-run"},
                ]})
            finally:
                root_allowlist_module.PROJECT = old_project
        self.assertIn("import BookFixture.Book", lines)
        self.assertIn("-- import Papers.PaperFixture.Paper", lines)

    def test_root_allowlist_accepts_valid_lifecycle_evidence(self):
        old_project = root_allowlist_module.PROJECT
        with tempfile.TemporaryDirectory() as temporary:
            project = Path(temporary)
            book = project / "Books" / "BookFixture"
            book.mkdir(parents=True)
            (book / "Book.lean").write_text("import Mathlib\n")
            root_allowlist_module.PROJECT = project
            try:
                lines = root_allowlist_module.expected_lines({
                    "schema_version": 1,
                    "projects": [{
                        "project": "book:BookFixture", "run_id": "checkpoint-run",
                        "run_result": "repair-incomplete",
                        "session_state": "checkpointed",
                        "project_state": "repair-checkpointed",
                        "resume": {
                            "last_checkpoint": "checkpoint-run", "current_root": "BookFixture.X",
                            "next_command": "lake build BookFixture.X", "branch": "repair/book",
                            "commit": "12345678",
                        },
                    }],
                })
            finally:
                root_allowlist_module.PROJECT = old_project
        self.assertIn("-- import BookFixture.Book", lines)
        self.assertNotIn("import BookFixture.Book", [line for line in lines if not line.startswith("--")])

    def test_root_allowlist_fingerprint_detects_project_drift(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            project = root / "ReasBook"
            book = project / "Books" / "Fixture"
            book.mkdir(parents=True)
            (book / "Book.lean").write_text("import Mathlib\n")
            subprocess.run(["git", "init", "-q"], cwd=root, check=True)
            subprocess.run(["git", "config", "user.name", "Fixture"], cwd=root, check=True)
            subprocess.run(["git", "config", "user.email", "fixture@example.test"], cwd=root, check=True)
            subprocess.run(["git", "add", "."], cwd=root, check=True)
            subprocess.run(["git", "commit", "-qm", "validated"], cwd=root, check=True)
            revision = subprocess.run(
                ["git", "rev-parse", "HEAD"], cwd=root, check=True, text=True,
                stdout=subprocess.PIPE,
            ).stdout.strip()
            spec = root_allowlist_module.discover(project)[0]
            self.assertTrue(root_allowlist_module.project_matches_revision(
                spec, revision, repo_root=root,
            ))
            (book / "New.lean").write_text("def drift := true\n")
            self.assertFalse(root_allowlist_module.project_matches_revision(
                spec, revision, repo_root=root,
            ))

    def test_project_lifecycle_manifest_rejects_duplicates(self):
        old_project = project_lifecycle_verifier.PROJECT
        with tempfile.TemporaryDirectory() as temporary:
            project = Path(temporary)
            book = project / "Books" / "BookFixture"
            book.mkdir(parents=True)
            (book / "Book.lean").write_text("import Mathlib\n")
            record = {
                "project": "book:BookFixture", "run_id": "pass-run",
                "run_result": "full-pass", "session_state": "completed",
                "project_state": "full-pass",
            }
            project_lifecycle_verifier.PROJECT = project
            try:
                findings = project_lifecycle_verifier.inspect_manifest({
                    "schema_version": 1, "migration_status": "complete",
                    "projects": [record, record],
                }, allow_partial=True)
            finally:
                project_lifecycle_verifier.PROJECT = old_project
        self.assertIn("duplicate lifecycle project", " ".join(findings))

    def test_disabled_missing_duplicate_and_quoted_module(self):
        with tempfile.TemporaryDirectory() as temporary:
            books = Path(temporary)
            book = books / "Fixture"
            book.mkdir()
            (book / "1_Digit.lean").write_text("")
            (book / "Missing.lean").write_text("")
            (book / "Book.lean").write_text(
                "import Fixture.«1_Digit»\nimport Fixture.«1_Digit»\n-- import Fixture.Missing\n"
            )
            spec = scope_module.ProjectSpec(
                "book", "Fixture", book, "Book.lean", "Fixture", "Fixture.Book"
            )
            result = coverage_module.inspect_project(spec)
            self.assertEqual(result["missing"], ["Fixture.Missing"])
            self.assertEqual(result["duplicates"], ["Fixture.«1_Digit»"])
            self.assertEqual(result["disabled"], ["Fixture.Missing"])

    def test_repair_target_uses_actual_library_module(self):
        self.assertEqual(
            fix_module._source_module_name("Fixture", "Chap01/1_Digit.lean"),
            "Fixture.Chap01.«1_Digit»",
        )
        old = fix_module.ACTIVE_KIND
        fix_module.ACTIVE_KIND = "paper"
        try:
            self.assertEqual(
                fix_module._source_module_name("Example", "Sections/1_Claim.lean"),
                "Papers.Example.Sections.«1_Claim»",
            )
        finally:
            fix_module.ACTIVE_KIND = old

    def test_sync_reactivates_historical_disabled_import(self):
        with tempfile.TemporaryDirectory() as temporary:
            book = Path(temporary) / "Fixture"
            book.mkdir()
            (book / "A.lean").write_text("")
            (book / "Book.lean").write_text(
                "-- MANUAL-DEGRADATION run=old toolchain=v4.29.0\n-- import Fixture.A\n"
            )
            sync_module._generate_book_lean(book, "Fixture")
            self.assertEqual(
                (book / "Book.lean").read_text(),
                "import Mathlib\nimport Fixture.A\n",
            )
            manifest = Path(temporary) / "degradations.json"
            manifest.write_text(json.dumps({"entries": [
                {"kind": "book", "name": "Fixture", "modules": ["Fixture.A"]},
                {"kind": "book", "name": "Other", "modules": ["Other.A"]},
            ]}))
            self.assertTrue(sync_module._clear_degradation("Fixture", manifest))
            self.assertEqual(
                [entry["name"] for entry in json.loads(manifest.read_text())["entries"]],
                ["Other"],
            )

    def test_destructive_sync_is_frozen_for_existing_projects(self):
        self.assertIn(
            "destructive synchronization is disabled",
            sync_module._legacy_mode_error(
                dry_run=False, legacy_destructive_sync=False,
                all_books=False, destination_exists=True,
            ),
        )
        self.assertIn(
            "permanently retired",
            sync_module._legacy_mode_error(
                dry_run=False, legacy_destructive_sync=True,
                all_books=False, destination_exists=True,
            ),
        )

    def test_legacy_destructive_sync_is_permanently_retired(self):
        self.assertIn(
            "permanently retired",
            sync_module._legacy_mode_error(
                dry_run=False, legacy_destructive_sync=True,
                all_books=True, destination_exists=False,
            ),
        )
        self.assertIn(
            "permanently retired",
            sync_module._legacy_mode_error(
                dry_run=True, legacy_destructive_sync=True,
                all_books=False, destination_exists=False,
            ),
        )
        self.assertIsNone(sync_module._legacy_mode_error(
            dry_run=True, legacy_destructive_sync=False,
            all_books=True, destination_exists=True,
        ))

    def test_sync_normalization_is_byte_stable(self):
        from lib.sync_three_way import tree_hash
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            source = root / "Nesterov"
            source.mkdir()
            (source / "A.lean").write_text("def a := 1\n")
            (source / "B.lean").write_text("import Nesterov.A\ndef b := a\n")
            paper = source / "Papers" / "Example" / "Paper.lean"
            paper.parent.mkdir(parents=True)
            paper.write_text("import Nesterov.A\n")
            (source / "lakefile.lean").write_text("package Nesterov\n")
            first, second = root / "first", root / "second"
            sync_module.normalize_book_tree(source, first, "Nesterov")
            sync_module.normalize_book_tree(source, second, "Nesterov")
            self.assertEqual(tree_hash(first), tree_hash(second))
            self.assertFalse((first / "lakefile.lean").exists())
            self.assertTrue((first / "Papers" / "Example" / "Paper.lean").is_file())
            self.assertEqual(
                (first / "Book.lean").read_text(),
                "import Mathlib\n"
                "import LecturesConvexOptimization_Nesterov_2018.A\n"
                "import LecturesConvexOptimization_Nesterov_2018.B\n",
            )
            profile = sync_module.normalization_profile("Nesterov")
            self.assertEqual(profile["id"], "Nesterov-v1")
            self.assertEqual(profile, sync_module.normalization_profile("Nesterov"))

    def test_paper_inventory_preview_is_read_only(self):
        with tempfile.TemporaryDirectory() as temporary:
            source = Path(temporary) / "PaperSource"
            source.mkdir()
            output = io.StringIO()
            with contextlib.redirect_stdout(output):
                sync_module.preview_paper(
                    source.parent, "PaperSource", "CanonicalPaper"
                )
            self.assertIn("[DRY RUN]", output.getvalue())
            self.assertIn("ReasBook/Papers/CanonicalPaper", output.getvalue())

    def test_sync_state_validator_checks_commit_hash_and_profile(self):
        payload = {
            "schema_version": 1,
            "source": {"name": "ALLBOOKS", "url": "https://example.test/ALLBOOKS.git"},
            "projects": {
                "book:LecturesConvexOptimization_Nesterov_2018": {
                    "source_directory": "Nesterov",
                    "accepted_upstream_commit": "a" * 40,
                    "normalization_profile": "Nesterov-v1",
                    "normalizer_commit": "b" * 40,
                    "normalized_tree_sha256": "c" * 64,
                    "accepted_in_reasbook_commit": "d" * 40,
                    "last_sync_report": "run-id",
                }
            },
        }
        self.assertEqual(sync_state_verifier.inspect(payload), [])
        payload["projects"]["book:LecturesConvexOptimization_Nesterov_2018"][
            "accepted_upstream_commit"
        ] = "short"
        self.assertIn("full SHA-1", " ".join(sync_state_verifier.inspect(payload)))

    def test_sync_state_validator_accepts_canonical_paper_profile(self):
        payload = {
            "schema_version": 1,
            "source": {"name": "ALLBOOKS", "url": "https://example.test/ALLBOOKS.git"},
            "projects": {
                "paper:SmoothMinimization_Nesterov_2004": {
                    "source_directory": "SmoothMinimization_Nesterov_2004",
                    "accepted_upstream_commit": "a" * 40,
                    "normalization_profile": (
                        "SmoothMinimization_Nesterov_2004-paper-"
                        "SmoothMinimization_Nesterov_2004-v1"
                    ),
                    "normalizer_commit": "b" * 40,
                    "normalized_tree_sha256": "c" * 64,
                    "accepted_in_reasbook_commit": "d" * 40,
                    "last_sync_report": "run-id",
                }
            },
        }
        self.assertEqual(sync_state_verifier.inspect(payload), [])

    def test_chapter1_profile_flattens_only_its_declared_source_directory(self):
        from lib.sync_three_way import tree_hash
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            source = root / "chapter1_reference_format_20260519_statement"
            nested = source / "chapter1_reference_format" / "Chap01"
            nested.mkdir(parents=True)
            (source / "chapter1_reference_format.lean").write_text(
                "import chapter1_reference_format.Chap01.A\n"
            )
            (nested / "A.lean").write_text("def a := 1\n")
            (source / "chapter1_reference_format" / "Book.lean").write_text("import Mathlib\n")
            first, second = root / "first", root / "second"
            for destination in (first, second):
                sync_module.normalize_book_tree(
                    source, destination, "chapter1_reference_format_20260519_statement"
                )
            self.assertEqual(tree_hash(first), tree_hash(second))
            self.assertTrue((first / "Chap01" / "A.lean").is_file())
            self.assertFalse((first / "chapter1_reference_format").exists())
            self.assertIn(
                "import chapter1_reference_format.Chap01.A",
                (first / "Book.lean").read_text(),
            )

    def test_rockafellar_profile_flattens_double_named_source_directory(self):
        from lib.sync_three_way import tree_hash
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            source = root / "ConvexAnalysis_Rockafellar_1970"
            nested = source / "ConvexAnalysis_Rockafellar_1970" / "Chap01"
            nested.mkdir(parents=True)
            (source / "ConvexAnalysis_Rockafellar_1970.lean").write_text(
                "import ConvexAnalysis_Rockafellar_1970.ConvexAnalysis_Rockafellar_1970.Chap01.A\n"
            )
            (nested / "A.lean").write_text("def a := 1\n")
            (source / "ConvexAnalysis_Rockafellar_1970" / "Book.lean").write_text(
                "import Mathlib\n"
            )
            first, second = root / "first", root / "second"
            for destination in (first, second):
                sync_module.normalize_book_tree(
                    source, destination, "ConvexAnalysis_Rockafellar_1970"
                )
            self.assertEqual(tree_hash(first), tree_hash(second))
            self.assertTrue((first / "Chap01" / "A.lean").is_file())
            self.assertFalse((first / "ConvexAnalysis_Rockafellar_1970").exists())
            self.assertIn(
                "import ConvexAnalysis_Rockafellar_1970.Chap01.A",
                (first / "ConvexAnalysis_Rockafellar_1970.lean").read_text(),
            )
            self.assertIn(
                "import ConvexAnalysis_Rockafellar_1970.Chap01.A",
                (first / "Book.lean").read_text(),
            )

    def test_paper_scope_excludes_compatibility_book_entry(self):
        with tempfile.TemporaryDirectory() as temporary:
            project = Path(temporary) / "ReasBook"
            paper = project / "Papers" / "Example"
            paper.mkdir(parents=True)
            (paper / "Claim.lean").write_text("")
            (paper / "Book.lean").write_text("import Mathlib\n")
            (paper / "Paper.lean").write_text("import Papers.Example.Claim\n")
            spec = scope_module.resolve(project, "paper", "Example")
            result = coverage_module.inspect_project(spec)
            self.assertTrue(result["ok"])
            self.assertEqual(result["target"], "Papers.Example.Paper")
            self.assertEqual(result["source_count"], 1)
            scope_module.generate_entry(spec)
            self.assertEqual(
                (paper / "Paper.lean").read_text(),
                "import Mathlib\nimport Papers.Example.Claim\n",
            )

    def test_toolchain_upgrade_updates_release_pins(self):
        source = 'require mathlib from git "x" @ "v4.30.0"\nrequire subverso from git "x" @ "verso-v4.30.0"\n'
        self.assertEqual(
            upgrade_module.update_version_pins(source, "4.30.0", "4.31.0"),
            'require mathlib from git "x" @ "v4.31.0"\nrequire subverso from git "x" @ "verso-v4.31.0"\n',
        )


class AutomationTests(RepositoryFixture):
    def test_parse_diagnostics_accepts_lean_430_and_legacy_formats(self):
        diagnostics = automation_module.parse_diagnostics(
            "error: Books/Fixture/Bad.lean:2:3: native failure\n"
            "Books/Fixture/Dependent.lean:4:5: error: legacy failure\n"
        )
        self.assertEqual(
            [(item["file"], item["line"], item["column"], item["message"])
             for item in diagnostics],
            [
                ("Books/Fixture/Bad.lean", "2", "3", "native failure"),
                ("Books/Fixture/Dependent.lean", "4", "5", "legacy failure"),
            ],
        )

    def test_paper_full_pass_uses_paper_target(self):
        marker = self.root / "paper-target"
        self.lake(f"echo \"$*\" >> {marker}\nexit 0\n")
        result = self.command(
            "run_automation.py", "--paper", "PaperFixture", "--run-id", "paper-pass"
        )
        self.assertEqual(result.returncode, 0, result.stdout)
        self.assertIn("build Papers.PaperFixture.Paper", marker.read_text())
        summary = self.root / "docs/automation-reports/v4.30.0/paper-pass/summary.md"
        self.assertIn("`paper:PaperFixture`", summary.read_text())

    def test_stale_degradation_manifest_is_rejected(self):
        manifest = self.root / "scripts/state/degradations.json"
        manifest.write_text(json.dumps({"entries": [{
            "kind": "book", "name": "Fixture", "modules": ["Fixture.Bad"],
            "source_run_id": "old", "toolchain": "4.30.0", "reason": "fixture",
            "restore_when": "fixed", "expires": "next review",
        }]}))
        result = self.command(
            "verify_import_coverage.py", "--book", "Fixture",
            "--approved-degradations", str(manifest), "--allow-approved-degradation",
        )
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("stale degradation approval", result.stdout)

    def test_build_exit_code_and_root_cascade_report(self):
        self.lake(
            "echo 'Books/Fixture/Bad.lean:1:1: error: fixture root failure'\n"
            "echo 'Books/Fixture/Dependent.lean:1:1: error: fixture cascade failure'\nexit 7\n"
        )
        result = self.command(
            "run_automation.py", "--book", "Fixture", "--run-id", "exit-fixture"
        )
        self.assertEqual(result.returncode, 7, result.stdout)
        report = self.root / "docs/automation-reports/v4.30.0/exit-fixture"
        self.assertEqual(
            {"summary.md", "diagnostics.json", "fixes.json", "import-coverage.json",
             "degradation-proposal.json", "lifecycle.json"} - {p.name for p in report.iterdir()},
            set(),
        )
        proposal = json.loads((report / "degradation-proposal.json").read_text())
        book = proposal["projects"]["book:Fixture"]
        self.assertEqual(book["root_modules"], ["Fixture.Bad"])
        self.assertEqual(book["diagnostic_modules"], ["Fixture.Bad", "Fixture.Dependent"])
        self.assertEqual(book["cascade_modules"], ["Fixture.Dependent"])
        self.assertIn("Mathlib revision: `fixture-revision`", (report / "summary.md").read_text())
        lifecycle = json.loads((report / "lifecycle.json").read_text())
        self.assertEqual(
            (lifecycle["run_result"], lifecycle["session_state"], lifecycle["project_state"]),
            ("repair-incomplete", "active", "repair-active"),
        )

    def test_checkpointed_run_requires_and_records_resume_evidence(self):
        self.lake("echo 'Books/Fixture/Bad.lean:1:1: error: remains'\nexit 1\n")
        missing = self.command(
            "run_automation.py", "--book", "Fixture", "--run-id", "missing-resume",
            "--session-state", "checkpointed",
        )
        self.assertEqual(missing.returncode, 2, missing.stdout)
        result = self.command(
            "run_automation.py", "--book", "Fixture", "--run-id", "with-resume",
            "--session-state", "checkpointed", "--last-checkpoint", "checkpoint-7",
            "--current-root", "Fixture.Bad", "--next-command", "lake build Fixture.Bad",
            "--resume-branch", "repair/fixture", "--resume-commit", "12345678",
        )
        self.assertEqual(result.returncode, 1, result.stdout)
        lifecycle = json.loads((
            self.root / "docs/automation-reports/v4.30.0/with-resume/lifecycle.json"
        ).read_text())
        self.assertEqual(lifecycle["project_state"], "repair-checkpointed")

    def test_repair_bootstrap_uses_real_library_target_and_run_directory(self):
        marker = self.root / "lake-arguments"
        self.lake(
            f"echo \"$*\" >> {marker}\n"
            "echo 'Books/Fixture/Bad.lean:1:1: error: fixture cannot repair'\nexit 1\n"
        )
        output = self.root / "repair-output"
        result = self.command(
            "fix_errors.py", "--bootstrap", "Fixture", "--apply",
            "--output-dir", str(output),
        )
        self.assertEqual(result.returncode, 0, result.stdout)
        self.assertIn("build Fixture.Book", marker.read_text())
        self.assertTrue(list(output.glob("repair-bootstrap-*-book-Fixture.md")))
        self.assertTrue((output / "repair-report-v4.30.0.md").is_file())

    def test_paper_repair_bootstrap_uses_paper_target(self):
        marker = self.root / "paper-repair-arguments"
        self.lake(
            f"echo \"$*\" >> {marker}\n"
            "echo 'Papers/PaperFixture/Claim.lean:1:1: error: fixture cannot repair'\nexit 1\n"
        )
        output = self.root / "paper-repair-output"
        result = self.command(
            "fix_errors.py", "--bootstrap", "PaperFixture", "--kind", "paper",
            "--apply", "--output-dir", str(output),
        )
        self.assertEqual(result.returncode, 0, result.stdout)
        self.assertIn("build Papers.PaperFixture.Paper", marker.read_text())
        self.assertTrue(list(output.glob("repair-bootstrap-*-paper-PaperFixture.md")))

    def test_repair_handoff_sanitizes_source_relative_group_name(self):
        output = self.root / "repair-output"
        previous_output = fix_module.REPORT_OUTPUT_DIR
        previous_root = fix_module.REPO_ROOT
        previous_project = fix_module.PROJECT_ROOT
        try:
            fix_module.REPORT_OUTPUT_DIR = output
            fix_module.REPO_ROOT = self.root
            fix_module.PROJECT_ROOT = self.project
            path = fix_module.write_cannot_fix_json(
                "Basic/EReal.lean", [{"file": "Bad.lean", "error": "failure"}]
            )
        finally:
            fix_module.REPORT_OUTPUT_DIR = previous_output
            fix_module.REPO_ROOT = previous_root
            fix_module.PROJECT_ROOT = previous_project

        self.assertEqual(path.parent, output)
        self.assertEqual(
            path.name, "repair-handoff-v4.30.0-book-Basic_EReal.lean.json"
        )
        self.assertTrue(path.is_file())

    def test_preflight_failure_is_infrastructure_and_skips_lake(self):
        marker = self.root / "lake-called"
        self.lake(f"touch {marker}\nexit 0\n")
        log = self.root / "preflight.log"
        log.write_text("network is unreachable\n")
        result = self.command(
            "run_automation.py", "--book", "Fixture", "--run-id", "infra-fixture",
            "--preflight-exit-code", "9", "--preflight-log", str(log),
        )
        self.assertEqual(result.returncode, 9)
        self.assertFalse(marker.exists())
        summary = self.root / "docs/automation-reports/v4.30.0/infra-fixture/summary.md"
        self.assertIn("`infrastructure-failure`", summary.read_text())

    def test_full_pass(self):
        self.lake("exit 0\n")
        result = self.command(
            "run_automation.py", "--book", "Fixture", "--run-id", "pass-fixture"
        )
        self.assertEqual(result.returncode, 0, result.stdout)
        summary = self.root / "docs/automation-reports/v4.30.0/pass-fixture/summary.md"
        self.assertIn("`full-pass`", summary.read_text())
        lifecycle = json.loads((summary.parent / "lifecycle.json").read_text())
        self.assertEqual(
            (lifecycle["session_state"], lifecycle["project_state"]),
            ("completed", "full-pass"),
        )

    def test_full_pass_can_approve_tip_candidate(self):
        self.lake("exit 0\n")
        compatibility = self.root / "docs" / "compatibility"
        compatibility.mkdir(parents=True)
        (compatibility / "v4.30.0.md").write_text("# Fixture\n")
        candidate = self.root / "candidate.json"
        candidate.write_text(json.dumps({
            "id": "TIP-4.30-998", "title": "automation fixture", "toolchain": "4.30.0",
            "diagnostic": "before", "preconditions": "fixture", "unsafe_cases": "others",
            "repair_pattern": "before -> after", "verification": "module and downstream",
            "provenance": "automation fixture", "reproducible_diagnostic": True,
            "module_build_pass": True, "downstream_checkpoint_pass": True,
            "no_proof_bypass": True, "automation_level": "suggest-only",
        }))
        result = self.command(
            "run_automation.py", "--book", "Fixture", "--run-id", "tip-fixture",
            "--tip-candidate", str(candidate),
        )
        self.assertEqual(result.returncode, 0, result.stdout)
        self.assertIn("TIP-4.30-998", (compatibility / "v4.30.0.md").read_text())

    def test_added_proof_bypass_prevents_full_pass(self):
        self.lake("exit 0\n")
        (self.book / "Bad.lean").write_text("axiom fixtureBypass : False\n")
        environment = self.env()
        environment["CI"] = "true"
        result = subprocess.run(
            [sys.executable, str(SCRIPTS / "run_automation.py"), "--book", "Fixture",
             "--run-id", "bypass-fixture"], cwd=self.root, env=environment,
            text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, check=False,
        )
        self.assertNotEqual(result.returncode, 0)
        report = self.root / "docs/automation-reports/v4.30.0/bypass-fixture"
        self.assertIn("`repair-incomplete`", (report / "summary.md").read_text())
        diagnostics = json.loads((report / "diagnostics.json").read_text())
        self.assertTrue(diagnostics["proof_bypass_findings"])

    def test_diff_check_prevents_full_pass(self):
        self.lake("exit 0\n")
        (self.book / "Bad.lean").write_text("def bad : Nat := 0   \n")
        result = self.command(
            "run_automation.py", "--book", "Fixture", "--run-id", "whitespace-fixture"
        )
        self.assertNotEqual(result.returncode, 0)
        diagnostics = json.loads((
            self.root / "docs/automation-reports/v4.30.0/whitespace-fixture/diagnostics.json"
        ).read_text())
        self.assertNotEqual(diagnostics["diff_check_exit_code"], 0)

    def test_scoped_audits_ignore_other_projects(self):
        self.lake("exit 0\n")
        (self.paper / "Claim.lean").write_text(
            "axiom unrelatedBypass : False   \n"
        )
        result = self.command(
            "run_automation.py", "--book", "Fixture", "--run-id", "scoped-audit-fixture"
        )
        self.assertEqual(result.returncode, 0, result.stdout)
        report = self.root / "docs/automation-reports/v4.30.0/scoped-audit-fixture"
        self.assertIn("`full-pass`", (report / "summary.md").read_text())
        diagnostics = json.loads((report / "diagnostics.json").read_text())
        self.assertEqual(diagnostics["proof_bypass_findings"], [])
        self.assertEqual(diagnostics["diff_check_exit_code"], 0)

    def test_approved_degradation_creates_new_report(self):
        self.lake("exit 0\n")
        source = self.root / "docs/automation-reports/v4.30.0/source-run"
        source.mkdir(parents=True)
        (source / "summary.md").write_text("# Source\n\n- Status: `repair-incomplete`\n")
        proposal = {
            "run_id": "source-run", "toolchain": "4.30.0", "status": "proposal-only",
            "projects": {"book:Fixture": {
                "kind": "book", "name": "Fixture",
                "root_modules": ["Fixture.Bad"],
                "cascade_modules": ["Fixture.Dependent"],
                "suggested_modules": ["Fixture.Bad", "Fixture.Dependent"],
                "approved_modules": [],
            }}, "applied": False,
        }
        (source / "degradation-proposal.json").write_text(json.dumps(proposal))
        rejected = self.command(
            "apply_degradation.py", "--run-id", "source-run", "--book", "Fixture",
            "--module", "Fixture.Bad", "--approve", "--reason", "temporary",
            "--restore-when", "fixed", "--expires", "next review",
        )
        self.assertNotEqual(rejected.returncode, 0)
        self.assertNotIn("MANUAL-DEGRADATION", (self.book / "Book.lean").read_text())
        result = self.command(
            "apply_degradation.py", "--run-id", "source-run", "--book", "Fixture",
            "--module", "Fixture.Bad", "--module", "Fixture.Dependent", "--approve",
            "--reason", "temporary upstream failure", "--restore-when", "root module passes",
            "--expires", "next toolchain review",
        )
        self.assertEqual(result.returncode, 0, result.stdout)
        self.assertEqual((source / "summary.md").read_text(), "# Source\n\n- Status: `repair-incomplete`\n")
        results = list(source.parent.glob("source-run-degraded-*"))
        self.assertEqual(len(results), 1)
        self.assertIn("`manually-degraded`", (results[0] / "summary.md").read_text())
        self.assertIn("MANUAL-DEGRADATION", (self.book / "Book.lean").read_text())
        manifest = json.loads((self.root / "scripts/state/degradations.json").read_text())
        self.assertEqual(manifest["entries"][0]["modules"], ["Fixture.Bad", "Fixture.Dependent"])
        gate = self.command(
            "run_automation.py", "--book", "Fixture", "--run-id", "degraded-gate",
            "--allow-approved-degradation",
        )
        self.assertEqual(gate.returncode, 0, gate.stdout)
        self.assertIn(
            "`manually-degraded`",
            (self.root / "docs/automation-reports/v4.30.0/degraded-gate/summary.md").read_text(),
        )

    def test_paper_degradation_uses_paper_entry_and_manifest_kind(self):
        self.lake("exit 0\n")
        source = self.root / "docs/automation-reports/v4.30.0/paper-source"
        source.mkdir(parents=True)
        (source / "summary.md").write_text("# Source\n\n- Status: `repair-incomplete`\n")
        (source / "degradation-proposal.json").write_text(json.dumps({
            "run_id": "paper-source", "toolchain": "4.30.0", "status": "proposal-only",
            "projects": {"paper:PaperFixture": {
                "kind": "paper", "name": "PaperFixture",
                "root_modules": ["Papers.PaperFixture.Claim"], "cascade_modules": [],
                "suggested_modules": ["Papers.PaperFixture.Claim"], "approved_modules": [],
            }}, "applied": False,
        }))
        result = self.command(
            "apply_degradation.py", "--run-id", "paper-source", "--paper", "PaperFixture",
            "--module", "Papers.PaperFixture.Claim", "--approve", "--reason", "fixture",
            "--restore-when", "claim passes", "--expires", "next review",
        )
        self.assertEqual(result.returncode, 0, result.stdout)
        self.assertIn("MANUAL-DEGRADATION", (self.paper / "Paper.lean").read_text())
        self.assertEqual((self.paper / "Book.lean").read_text(), "import Mathlib\n")
        entry = json.loads((self.root / "scripts/state/degradations.json").read_text())["entries"][0]
        self.assertEqual((entry["kind"], entry["name"]), ("paper", "PaperFixture"))


class TipTests(RepositoryFixture):
    def setUp(self):
        super().setUp()
        compatibility = self.root / "docs" / "compatibility"
        compatibility.mkdir(parents=True)
        (compatibility / "v4.30.0.md").write_text("# Fixture compatibility\n")
        (compatibility / "migrations-v4.30.0.json").write_text("{}\n")

    def test_tip_and_migration_are_idempotent(self):
        candidate = self.root / "candidate.json"
        candidate.write_text(json.dumps({
            "id": "TIP-4.30-999", "title": "fixture", "toolchain": "4.30.0",
            "diagnostic": "before", "preconditions": "exact fixture",
            "unsafe_cases": "other contexts", "repair_pattern": "before -> after",
            "verification": "two fixture builds", "provenance": "run fixture",
            "reproducible_diagnostic": True, "module_build_pass": True,
            "downstream_checkpoint_pass": True, "no_proof_bypass": True,
            "automation_level": "safe-auto-fix", "status": "confirmed",
            "verified_fixtures": ["one", "two"], "promote_to_migration": True,
            "old_identifier": "oldFixture", "new_identifier": "newFixture",
            "migration_note": "fixture rename",
        }))
        first = self.command("update_compatibility_tips.py", str(candidate))
        before = (self.root / "docs/compatibility/v4.30.0.md").read_text()
        second = self.command("update_compatibility_tips.py", str(candidate))
        after = (self.root / "docs/compatibility/v4.30.0.md").read_text()
        self.assertEqual(first.returncode, 0, first.stdout)
        self.assertEqual(second.returncode, 0, second.stdout)
        self.assertEqual(before, after)
        rules = json.loads((self.root / "docs/compatibility/migrations-v4.30.0.json").read_text())
        self.assertEqual(rules["oldFixture"]["provenance"], "TIP-4.30-999")
        env = self.env()
        env["PYTHONPATH"] = str(SCRIPTS)
        loaded = subprocess.run(
            [sys.executable, "-c", "from lib.migration_table import find_migration; print(find_migration('oldFixture')['provenance'])"],
            env=env, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, check=False,
        )
        self.assertEqual(loaded.returncode, 0, loaded.stdout)
        self.assertEqual(loaded.stdout.strip(), "TIP-4.30-999")


class WorkflowContractTests(unittest.TestCase):
    def test_wrappers_use_reusable_workflow_and_never_push_or_upload_reports(self):
        root = SCRIPTS.parent
        workflows = root / ".github" / "workflows"
        for name in ("build.yml", "sync-from-a.yml", "repair.yml"):
            self.assertIn(
                "uses: ./.github/workflows/automation.yml",
                (workflows / name).read_text(),
            )
        self.assertIn(
            "uses: ./.github/workflows/automation.yml",
            (workflows / "check-toolchain.yml").read_text(),
        )
        combined = "\n".join(path.read_text() for path in workflows.glob("*.yml"))
        self.assertNotIn("git push", combined)
        self.assertNotIn("actions/upload-artifact", combined)
        core = (workflows / "automation.yml").read_text()
        self.assertIn("group: lean-resource-lock", core)
        self.assertIn("scripts/ci_heartbeat.sh automation", core)
        self.assertIn("python3 scripts/run_automation.py", core)
        self.assertIn("peter-evans/create-pull-request@v7", core)
        self.assertIn("args+=(--paper \"$PAPER\")", core)
        repair = (workflows / "repair.yml").read_text()
        self.assertIn("options: [book, paper]", repair)

    def test_sync_workflow_is_single_project_three_way_only(self):
        workflows = SCRIPTS.parent / ".github" / "workflows"
        reusable = (workflows / "automation.yml").read_text()
        wrapper = (workflows / "sync-from-a.yml").read_text()
        self.assertIn("--to-commit", reusable)
        self.assertIn("--apply .automation/sync-plan/sync-plan.json", reusable)
        self.assertIn("--accept-sync .automation/sync-plan/sync-plan.json", reusable)
        self.assertIn("sync requires exactly one book or paper", reusable)
        self.assertIn('project_key="paper:$PAPER"', reusable)
        self.assertNotIn("sync_from_a.py --source .automation/source-a --all", reusable)
        self.assertIn("required: true", wrapper)
        self.assertIn("--all --dry-run", wrapper)

    def test_heartbeat_preserves_exit_code(self):
        result = subprocess.run(
            [str(SCRIPTS / "ci_heartbeat.sh"), "fixture", "sh", "-c", "exit 7"],
            text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, check=False,
        )
        self.assertEqual(result.returncode, 7, result.stdout)


if __name__ == "__main__":
    unittest.main()
