from __future__ import annotations

import tempfile
import unittest
from unittest.mock import patch
from pathlib import Path
import sys
import json
import subprocess

SCRIPTS = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(SCRIPTS))

from lib.sync_three_way import apply_staged_tree, plan_tree_merge, read_tree, tree_hash
import sync_from_a


class ThreeWayTreeTests(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory()
        self.root = Path(self.temporary.name)
        self.base = self.root / "base"
        self.ours = self.root / "ours"
        self.theirs = self.root / "theirs"
        self.merged = self.root / "merged"
        for tree in (self.base, self.ours, self.theirs):
            tree.mkdir()

    def tearDown(self):
        self.temporary.cleanup()

    @staticmethod
    def put(root: Path, relative: str, text: str) -> None:
        path = root / relative
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(text)

    def test_upstream_and_local_only_changes_are_both_preserved(self):
        for tree in (self.base, self.ours, self.theirs):
            self.put(tree, "Common.lean", "base\n")
            self.put(tree, "Local.lean", "base local\n")
        self.put(self.ours, "Local.lean", "repaired local\n")
        self.put(self.theirs, "Upstream.lean", "new upstream\n")
        plan = plan_tree_merge(self.base, self.ours, self.theirs, self.merged)
        merged = read_tree(self.merged)
        self.assertEqual(merged["Local.lean"], b"repaired local\n")
        self.assertEqual(merged["Upstream.lean"], b"new upstream\n")
        classes = {item["path"]: item["classification"] for item in plan["entries"]}
        self.assertEqual(classes["Local.lean"], "local-only")
        self.assertEqual(classes["Upstream.lean"], "upstream-only")
        self.assertEqual(plan["conflicts"], [])

    def test_tree_reader_ignores_nested_lake_build_artifacts(self):
        self.put(self.base, "Source.lean", "def source := 1\n")
        self.put(self.base, ".lake/packages/dependency/Generated.lean", "def cache := 1\n")
        tree = read_tree(self.base)
        self.assertEqual(set(tree), {"Source.lean"})
        without_cache = self.root / "without-cache"
        without_cache.mkdir()
        self.put(without_cache, "Source.lean", "def source := 1\n")
        self.assertEqual(tree_hash(self.base), tree_hash(without_cache))

    def test_non_overlapping_text_changes_auto_merge(self):
        base = "first\nmiddle\nlast\n"
        self.put(self.base, "Both.lean", base)
        self.put(self.ours, "Both.lean", "local first\nmiddle\nlast\n")
        self.put(self.theirs, "Both.lean", "first\nmiddle\nupstream last\n")
        plan = plan_tree_merge(self.base, self.ours, self.theirs, self.merged)
        self.assertEqual(plan["conflicts"], [])
        self.assertEqual(
            (self.merged / "Both.lean").read_text(),
            "local first\nmiddle\nupstream last\n",
        )

    def test_overlapping_changes_are_not_applied_to_staged_tree(self):
        self.put(self.base, "Both.lean", "value\n")
        self.put(self.ours, "Both.lean", "local\n")
        self.put(self.theirs, "Both.lean", "upstream\n")
        plan = plan_tree_merge(self.base, self.ours, self.theirs, self.merged)
        self.assertEqual(plan["conflicts"][0]["conflict_type"], "modify/modify")
        self.assertFalse((self.merged / "Both.lean").exists())

    def test_exact_rename_transports_local_modification(self):
        self.put(self.base, "Old.lean", "base\n")
        self.put(self.ours, "Old.lean", "local repair\n")
        self.put(self.theirs, "New.lean", "base\n")
        plan = plan_tree_merge(self.base, self.ours, self.theirs, self.merged)
        self.assertEqual(plan["exact_renames"], {"Old.lean": "New.lean"})
        self.assertEqual((self.merged / "New.lean").read_text(), "local repair\n")
        self.assertFalse((self.merged / "Old.lean").exists())
        self.assertEqual(plan["conflicts"], [])

    def test_delete_modify_is_a_conflict(self):
        self.put(self.base, "Removed.lean", "base\n")
        self.put(self.ours, "Removed.lean", "local repair\n")
        plan = plan_tree_merge(self.base, self.ours, self.theirs, self.merged)
        self.assertEqual(plan["conflicts"][0]["conflict_type"], "delete/modify")

    def test_apply_failure_restores_original_tree(self):
        self.put(self.ours, "A.lean", "original\n")
        self.put(self.merged, "A.lean", "replacement\n")
        before = tree_hash(self.ours)
        with self.assertRaisesRegex(RuntimeError, "injected"):
            apply_staged_tree(self.merged, self.ours, inject_failure_after_backup=True)
        self.assertEqual(tree_hash(self.ours), before)
        self.assertEqual((self.ours / "A.lean").read_text(), "original\n")


class ExactCommitSyncTests(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory()
        self.root = Path(self.temporary.name)
        self.source = self.root / "ALLBOOKS"
        self.repo = self.root / "ReasBook-private"
        self.source.mkdir()
        self.repo.mkdir()
        for repository in (self.source, self.repo):
            subprocess.run(["git", "init", "-q"], cwd=repository, check=True)
            subprocess.run(["git", "config", "user.name", "Fixture"], cwd=repository, check=True)
            subprocess.run(["git", "config", "user.email", "fixture@example.test"], cwd=repository, check=True)
        project = self.source / "Nesterov"
        project.mkdir()
        (project / "A.lean").write_text("def value := 1\n")
        self._commit(self.source, "base")
        self.base_commit = self._head(self.source)

        self.target = self.repo / "ReasBook" / "Books" / "LecturesConvexOptimization_Nesterov_2018"
        self.target.parent.mkdir(parents=True)
        sync_from_a.normalize_book_tree(project, self.target, "Nesterov")
        self.base_tree_hash = tree_hash(self.target)
        (self.target / "A.lean").write_text("def value := 1\n\n-- local repair\n")
        (self.repo / ".gitignore").write_text("docs/\n")
        docs = self.repo / "docs"
        docs.mkdir()
        state_dir = self.repo / "scripts" / "state"
        state_dir.mkdir(parents=True)
        (state_dir / "degradations.json").write_text(json.dumps({"entries": [{
            "kind": "book", "name": "LecturesConvexOptimization_Nesterov_2018",
            "modules": ["Example"],
        }, {"kind": "book", "name": "Other", "modules": ["Other.X"]}]}))
        self._commit(self.repo, "local repair")

        (project / "B.lean").write_text("import Nesterov.A\ndef upstream := value\n")
        self._commit(self.source, "upstream")
        self.target_commit = self._head(self.source)
        self.state = self.repo / "scripts" / "state" / "sync-state.json"
        self.state.parent.mkdir(parents=True, exist_ok=True)
        self.state.write_text(json.dumps({
            "schema_version": 1,
            "source": {"name": "ALLBOOKS", "url": "fixture"},
            "projects": {
                "book:LecturesConvexOptimization_Nesterov_2018": {
                    "source_directory": "Nesterov",
                    "accepted_upstream_commit": self.base_commit,
                    "normalization_profile": "Nesterov-v1",
                    "normalizer_commit": "fixture",
                    "normalized_tree_sha256": self.base_tree_hash,
                    "accepted_in_reasbook_commit": self._head(self.repo),
                    "last_sync_report": "baseline",
                }
            },
        }))

    def tearDown(self):
        self.temporary.cleanup()

    @staticmethod
    def _commit(repository: Path, message: str) -> None:
        subprocess.run(["git", "add", "."], cwd=repository, check=True)
        subprocess.run(["git", "commit", "-qm", message], cwd=repository, check=True)

    @staticmethod
    def _head(repository: Path) -> str:
        return subprocess.run(
            ["git", "rev-parse", "HEAD"], cwd=repository, check=True,
            text=True, stdout=subprocess.PIPE,
        ).stdout.strip()

    def test_exact_commit_plan_and_apply_preserve_local_repairs(self):
        report = self.repo / "docs" / "sync-plan"
        plan = sync_from_a.create_sync_plan(
            source_repo=self.source, dir_name="Nesterov", to_commit=self.target_commit,
            report_dir=report, state_path=self.state, repo_root=self.repo,
            books_dir=self.target.parent,
        )
        self.assertEqual(plan["conflicts"], [])
        self.assertEqual(plan["base_upstream_commit"], self.base_commit)
        self.assertEqual(plan["target_upstream_commit"], self.target_commit)
        self.assertEqual(
            set(plan["review_category_counts"]),
            {"upstream-only", "local-only", "auto-merged", "conflicted", "deleted", "renamed"},
        )
        summary = (report / "summary.md").read_text()
        for category in plan["review_category_counts"]:
            self.assertIn(f"`{category}`:", summary)
        for artifact in ("upstream.diff", "local.diff", "auto-merge.diff", "conflicts.json"):
            self.assertTrue((report / artifact).is_file())
        self.assertIn("B.lean", (report / "upstream.diff").read_text())
        self.assertIn("local repair", (report / "local.diff").read_text())
        sync_from_a.apply_sync_plan(report / "sync-plan.json", repo_root=self.repo)
        self.assertIn("local repair", (self.target / "A.lean").read_text())
        self.assertTrue((self.target / "B.lean").is_file())
        degradations = json.loads((self.repo / "scripts/state/degradations.json").read_text())
        self.assertEqual([entry["name"] for entry in degradations["entries"]], ["Other"])

    def test_paper_plan_and_apply_use_exact_canonical_paper_scope(self):
        source_name = "PaperSource"
        paper_name = "PaperFixture"
        source_project = self.source / source_name
        paper_source = source_project / "Papers" / paper_name
        paper_source.mkdir(parents=True)
        (paper_source / "A.lean").write_text("def paperValue := 1\n")
        (paper_source / "Paper.lean").write_text("import Papers.PaperFixture.A\n")
        self._commit(self.source, "paper base")
        paper_base = self._head(self.source)

        paper_target = self.repo / "ReasBook" / "Papers" / paper_name
        paper_target.parent.mkdir(parents=True)
        with patch.dict(sync_from_a.PAPER_SOURCE_PROJECTS, {source_name: paper_name}):
            sync_from_a.normalize_paper_tree(
                source_project, paper_target, source_name, paper_name
            )
            self._commit(self.repo, "paper baseline")
            state = json.loads(self.state.read_text())
            state["projects"][f"paper:{paper_name}"] = {
                "source_directory": source_name,
                "accepted_upstream_commit": paper_base,
                "normalization_profile": sync_from_a.paper_normalization_profile(
                    source_name, paper_name
                )["id"],
                "normalizer_commit": "fixture",
                "normalized_tree_sha256": tree_hash(paper_target),
                "accepted_in_reasbook_commit": self._head(self.repo),
                "last_sync_report": "paper baseline",
            }
            self.state.write_text(json.dumps(state))
            (paper_source / "B.lean").write_text(
                "import Papers.PaperFixture.A\ndef paperUpstream := paperValue\n"
            )
            self._commit(self.source, "paper upstream")
            report = self.repo / "docs" / "paper-sync-plan"
            plan = sync_from_a.create_sync_plan(
                source_repo=self.source, dir_name=source_name,
                to_commit=self._head(self.source), report_dir=report,
                state_path=self.state, repo_root=self.repo,
                kind="paper", project_name=paper_name,
                papers_dir=paper_target.parent,
            )
            self.assertEqual(plan["project"], f"paper:{paper_name}")
            self.assertEqual(plan["target_path"], f"ReasBook/Papers/{paper_name}")
            sync_from_a.apply_sync_plan(report / "sync-plan.json", repo_root=self.repo)
        self.assertTrue((paper_target / "B.lean").is_file())
        paper_entry = (paper_target / "Paper.lean").read_text()
        self.assertIn("import Papers.PaperFixture.B", paper_entry)
        self.assertNotIn("import Papers.PaperFixture.Paper", paper_entry)

    def test_baseline_hash_mismatch_fails_without_report_or_tree_change(self):
        payload = json.loads(self.state.read_text())
        payload["projects"]["book:LecturesConvexOptimization_Nesterov_2018"][
            "normalized_tree_sha256"
        ] = "0" * 64
        self.state.write_text(json.dumps(payload))
        before = tree_hash(self.target)
        report = self.repo / "docs" / "bad-plan"
        with self.assertRaisesRegex(ValueError, "baseline hash mismatch"):
            sync_from_a.create_sync_plan(
                source_repo=self.source, dir_name="Nesterov", to_commit=self.target_commit,
                report_dir=report, state_path=self.state, repo_root=self.repo,
                books_dir=self.target.parent,
            )
        self.assertFalse(report.exists())
        self.assertEqual(tree_hash(self.target), before)

    def test_baseline_candidate_requires_explicit_reconciliation(self):
        report = self.repo / "docs" / "baseline-candidate"
        candidate = sync_from_a.create_baseline_candidate(
            source_repo=self.source, dir_name="Nesterov", at_commit=self.base_commit,
            report_dir=report, repo_root=self.repo, books_dir=self.target.parent,
        )
        self.assertFalse(candidate["exact_match"])
        fresh_state = self.repo / "scripts" / "state" / "fresh-sync-state.json"
        with self.assertRaisesRegex(ValueError, "approve-reconciliation"):
            sync_from_a.accept_baseline_candidate(
                report / "baseline-candidate.json", fresh_state, reason="reviewed",
            )
        accepted = sync_from_a.accept_baseline_candidate(
            report / "baseline-candidate.json", fresh_state,
            reason="local.diff is the committed Lean compatibility repair",
            approve_reconciliation=True,
        )
        self.assertEqual(accepted["accepted_upstream_commit"], self.base_commit)

    def test_sync_state_advances_only_with_full_pass_lifecycle(self):
        report = self.repo / "docs" / "sync-plan-accept"
        sync_from_a.create_sync_plan(
            source_repo=self.source, dir_name="Nesterov", to_commit=self.target_commit,
            report_dir=report, state_path=self.state, repo_root=self.repo,
            books_dir=self.target.parent,
        )
        sync_from_a.apply_sync_plan(report / "sync-plan.json", repo_root=self.repo)
        self._commit(self.repo, "apply sync")
        verified_head = self._head(self.repo)
        automation = self.repo / "docs" / "automation"
        automation.mkdir()
        (automation / "lifecycle.json").write_text(json.dumps({
            "project": "book:LecturesConvexOptimization_Nesterov_2018",
            "run_result": "repair-incomplete", "session_state": "active",
            "project_state": "repair-active", "target_revision": verified_head,
        }))
        with self.assertRaisesRegex(ValueError, "does not prove full-pass"):
            sync_from_a.accept_verified_sync(report / "sync-plan.json", automation, self.state)
        before = json.loads(self.state.read_text())["projects"][
            "book:LecturesConvexOptimization_Nesterov_2018"
        ]["accepted_upstream_commit"]
        self.assertEqual(before, self.base_commit)
        (automation / "lifecycle.json").write_text(json.dumps({
            "project": "book:LecturesConvexOptimization_Nesterov_2018",
            "run_result": "full-pass", "session_state": "completed",
            "project_state": "full-pass", "target_revision": verified_head,
        }))
        accepted = sync_from_a.accept_verified_sync(
            report / "sync-plan.json", automation, self.state, repo_root=self.repo,
        )
        self.assertEqual(accepted["accepted_upstream_commit"], self.target_commit)
        self.assertEqual(accepted["accepted_in_reasbook_commit"], verified_head)


if __name__ == "__main__":
    unittest.main()
