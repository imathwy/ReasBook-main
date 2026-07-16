from __future__ import annotations

import importlib.util
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
import lib.project_scope as scope_module


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
        (docs / "degradations.json").write_text('{"entries": []}\n')
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
        manifest = self.root / "docs/degradations.json"
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
             "degradation-proposal.json"} - {p.name for p in report.iterdir()},
            set(),
        )
        proposal = json.loads((report / "degradation-proposal.json").read_text())
        book = proposal["projects"]["book:Fixture"]
        self.assertEqual(book["root_modules"], ["Fixture.Bad"])
        self.assertEqual(book["diagnostic_modules"], ["Fixture.Bad", "Fixture.Dependent"])
        self.assertEqual(book["cascade_modules"], ["Fixture.Dependent"])
        self.assertIn("Mathlib revision: `fixture-revision`", (report / "summary.md").read_text())

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
        manifest = json.loads((self.root / "docs/degradations.json").read_text())
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
        entry = json.loads((self.root / "docs/degradations.json").read_text())["entries"][0]
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

    def test_heartbeat_preserves_exit_code(self):
        result = subprocess.run(
            [str(SCRIPTS / "ci_heartbeat.sh"), "fixture", "sh", "-c", "exit 7"],
            text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, check=False,
        )
        self.assertEqual(result.returncode, 7, result.stdout)


if __name__ == "__main__":
    unittest.main()
