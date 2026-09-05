from __future__ import annotations

import tempfile
import unittest
from pathlib import Path

from reasbook_deploy_sdk.errors import DeployConfigError
from reasbook_deploy_sdk.release.results import ProjectBuildResult, StageOutcome
from reasbook_deploy_sdk.release.store import ReleaseLayout


class ProjectBuildResultTests(unittest.TestCase):
    def test_success_round_trip_preserves_artifact_identity(self) -> None:
        result = ProjectBuildResult(
            project_key="books/Demo.Book",
            branch="v4.30.0",
            commit="a" * 40,
            status="success",
            site_root="/cache/project-finalizers/v4.30.0/books_Demo.Book/site",
            stages=(
                StageOutcome("preflight", "success"),
                StageOutcome("docs", "skipped", "not requested"),
                StageOutcome("stage-site", "success"),
            ),
            site_tree_sha256="sha256:" + "b" * 64,
            file_count=7,
            total_bytes=4096,
        )

        self.assertTrue(result.succeeded)
        self.assertEqual(
            ProjectBuildResult.from_dict(result.public_dict()),
            result,
        )

    def test_failed_result_has_no_publishable_artifact(self) -> None:
        result = ProjectBuildResult(
            project_key="papers/Demo",
            branch="v4.26.0",
            commit="c" * 40,
            status="failed",
            site_root=None,
            stages=(StageOutcome("verso", "failed"),),
            error="fixture failure",
        )

        self.assertFalse(result.succeeded)
        self.assertEqual(ProjectBuildResult.from_dict(result.public_dict()), result)
        with self.assertRaisesRegex(DeployConfigError, "must not publish"):
            ProjectBuildResult(
                project_key="papers/Demo",
                branch="v4.26.0",
                commit="c" * 40,
                status="failed",
                site_root="/stale/site",
                stages=(),
            )

    def test_success_requires_nonempty_digest_bound_site(self) -> None:
        common = {
            "project_key": "books/Demo",
            "branch": "v4.30.0",
            "commit": "d" * 40,
            "status": "success",
            "site_root": "/site",
            "stages": (StageOutcome("stage-site", "success"),),
            "site_tree_sha256": "sha256:" + "e" * 64,
            "file_count": 1,
            "total_bytes": 1,
        }
        for override in (
            {"site_root": None},
            {"site_tree_sha256": None},
            {"site_tree_sha256": "sha256:short"},
            {"file_count": 0},
            {"total_bytes": 0},
        ):
            with self.subTest(override=override), self.assertRaises(DeployConfigError):
                ProjectBuildResult(**(common | override))

    def test_rejects_unsafe_or_incoherent_identity(self) -> None:
        common = {
            "project_key": "books/Demo",
            "branch": "v4.30.0",
            "commit": "f" * 40,
            "status": "failed",
            "site_root": None,
            "stages": (),
        }
        for override in (
            {"project_key": "../Demo"},
            {"project_key": "books/Demo/child"},
            {"branch": "main"},
            {"commit": "short"},
            {"status": "degraded"},
            {"file_count": True},
            {"total_bytes": -1},
        ):
            with self.subTest(override=override), self.assertRaises(DeployConfigError):
                ProjectBuildResult(**(common | override))


class ProjectFinalizerLayoutTests(unittest.TestCase):
    def test_project_paths_are_isolated_from_branch_outputs_and_logs(self) -> None:
        with tempfile.TemporaryDirectory() as temp:
            layout = ReleaseLayout(
                Path(temp) / "cache",
                "site-20260905T120000Z-" + "a" * 12,
            )

            root = layout.root / "project-finalizers" / "v4.30.0" / "books_Demo.Book"
            self.assertEqual(
                layout.project_finalizer_root("v4.30.0", "books/Demo.Book"),
                root,
            )
            self.assertEqual(
                layout.project_finalizer_site("v4.30.0", "books/Demo.Book"),
                root / "site",
            )
            self.assertEqual(
                layout.project_finalizer_result("v4.30.0", "books/Demo.Book"),
                root / "result.json",
            )
            self.assertEqual(
                layout.project_finalizer_logs("v4.30.0", "books/Demo.Book"),
                layout.logs / "v4.30.0" / "projects" / "books_Demo.Book",
            )
            self.assertNotEqual(root.parent, layout.branch_sites / "v4.30.0")

    def test_kind_is_part_of_safe_project_component(self) -> None:
        layout = ReleaseLayout("/cache", "site-20260905T120000Z-" + "b" * 12)
        self.assertNotEqual(
            layout.project_finalizer_root("v4.30.0", "books/Demo"),
            layout.project_finalizer_root("v4.30.0", "papers/Demo"),
        )

    def test_project_paths_reject_unsafe_external_identity(self) -> None:
        layout = ReleaseLayout("/cache", "site-20260905T120000Z-" + "c" * 12)
        for branch, project_key in (
            ("main", "books/Demo"),
            ("v4.30.0", "../Demo"),
            ("v4.30.0", "books/Demo/child"),
            ("v4.30.0/../../escape", "books/Demo"),
        ):
            with self.subTest(branch=branch, project_key=project_key):
                with self.assertRaises(DeployConfigError):
                    layout.project_finalizer_root(branch, project_key)


if __name__ == "__main__":
    unittest.main()
