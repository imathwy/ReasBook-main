from __future__ import annotations

import json
from pathlib import Path
import sys
import subprocess
import tempfile
import unittest
from unittest.mock import patch

from reasbook_deploy_sdk import (
    DEFAULT_CACHE_ROOT,
    DeployConfigError,
    DeployExecutionError,
    DeploymentConfig,
    GitClient,
    prepare_cache_dirs,
    safe_name,
)
from reasbook_deploy_sdk.ci import _valid_branch, heartbeat, prepare_cache, retry_on_143


class DeploySdkTests(unittest.TestCase):
    def test_config_resolves_paths_and_disables_dependent_builds(self) -> None:
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            repo = root / "repo"
            config = DeploymentConfig(
                repo_root=repo,
                reviewer_root=root / "reviewer",
                data_root=root / "data",
                cache_root=root / "cache",
                books=("Book",),
                build=False,
                build_docs=True,
                build_stacks=True,
            ).resolved()
            self.assertFalse(config.build_docs)
            self.assertFalse(config.build_stacks)
            self.assertTrue(config.repo_root.is_absolute())

    def test_config_rejects_cache_inside_checkout(self) -> None:
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            with self.assertRaises(DeployConfigError):
                DeploymentConfig(
                    repo_root=root,
                    reviewer_root=root / "reviewer",
                    data_root=root / "data",
                    cache_root=root / "nested-cache",
                ).resolved()

    def test_cache_layout_is_explicit(self) -> None:
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            prepare_cache_dirs(root)
            self.assertEqual(
                {path.name for path in root.iterdir()},
                {"sources", "lake", "docs", "sites", "mathlib", "xdg", "logs", "locks", "manifests"},
            )

    def test_cli_defaults_to_fixed_cache_root(self) -> None:
        from reasbook_deploy_sdk.cli import build_parser

        args = build_parser(Path("/tmp/reasbook-parser-test")).parse_args([])
        self.assertEqual(args.cache_root, DEFAULT_CACHE_ROOT)
        self.assertEqual(args.reviewer_root, Path("/tmp/reasbook-parser-test/apps/reasbook-reviewer"))

    def test_integrated_reviewer_uses_shared_cache_without_building(self) -> None:
        from reasbook_deploy_sdk.cli import _deployment_config, build_parser
        from reasbook_deploy_sdk.reviewer import reviewer_environment

        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            repo = root / "ReasBook"
            cache = root / "cache"
            with patch.dict("os.environ", {}, clear=True):
                args = build_parser(repo).parse_args(["--cache-root", str(cache), "--no-stacks", "--no-build"])
                config = _deployment_config(args).resolved()
            self.assertEqual(config.data_root, cache / "reviewer" / "data")
            self.assertFalse(config.build)
            self.assertFalse(cache.exists())
            environment = reviewer_environment(
                repo_root=repo, data_root=config.data_root, cache_root=cache,
                host="127.0.0.1", port=3000, python_bin=sys.executable, base={},
            )
            self.assertEqual(environment["REASBOOK_CACHE_ROOT"], str(cache))
            self.assertEqual(environment["REASBOOK_REVIEWER_RELEASE_ROOT"], str(cache / "releases"))
            self.assertEqual(environment["REASBOOK_REVIEWER_CATALOG"], str(config.data_root / "catalog.json"))
            with self.assertRaises(DeployConfigError):
                DeploymentConfig(
                    repo_root=repo, reviewer_root=repo / "apps" / "reasbook-reviewer",
                    data_root=cache / "sources", cache_root=cache,
                ).resolved()

    def test_branch_and_name_safety(self) -> None:
        self.assertTrue(_valid_branch("v4.30.0"))
        self.assertFalse(_valid_branch("../tmp"))
        self.assertFalse(_valid_branch(""))
        self.assertEqual(safe_name("v4.30.0/rc"), "v4.30.0_rc")

    def test_git_branch_selection_uses_version_order(self) -> None:
        client = GitClient()

        with patch.object(client, "available_branches", return_value=["v4.30.0", "v4.26.0"]), patch.object(
            client, "branch_ref", return_value="origin/v4.30.0"
        ), patch.object(client, "_run") as run:
            from reasbook_sdk_common import CommandResult

            run.return_value = CommandResult(argv=("git",), returncode=0)
            self.assertEqual(client.choose_branch(Path("/repo"), "Book", None), "v4.30.0")

    def test_empty_persist_root_uses_fixed_cache(self) -> None:
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp) / "repo"
            home = Path(temp) / "home"
            root.mkdir()
            values = {
                "PERSIST_ROOT": "",
                "HOME": str(home),
                "GITHUB_REPOSITORY": "acme/books",
            }
            fixed_cache = root.parent / "fixed-cache"
            with patch("reasbook_deploy_sdk.ci.DEFAULT_CACHE_ROOT", fixed_cache):
                selected = prepare_cache("v4.30.0", repo_root=root, environ=values)
            self.assertEqual(selected, fixed_cache / "ci" / "acme_books" / "v4.30.0")
            self.assertEqual(DEFAULT_CACHE_ROOT, Path("/volume/math/users/zcwang/ReasBook_Reviewer/cache/reasbook"))

    def test_cache_root_override_applies_to_ci_helper(self) -> None:
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            repo = root / "repo"
            repo.mkdir()
            override = root / "override-cache"
            selected = prepare_cache(
                "v4.30.0",
                repo_root=repo,
                environ={
                    "PERSIST_ROOT": "",
                    "REASBOOK_CACHE_ROOT": str(override),
                    "GITHUB_REPOSITORY": "acme/books",
                },
            )
            self.assertEqual(selected, override / "ci" / "acme_books" / "v4.30.0")

    def test_heartbeat_preserves_shell_signal_status(self) -> None:
        command = [
            sys.executable,
            "-c",
            "import os, signal; os.kill(os.getpid(), signal.SIGTERM)",
        ]
        self.assertEqual(
            heartbeat("signal", command, environ={"HEARTBEAT_INTERVAL_SECONDS": "1"}),
            143,
        )

    def test_retry_maps_signal_status_before_deciding_to_retry(self) -> None:
        command = [
            sys.executable,
            "-c",
            "import os, signal; os.kill(os.getpid(), signal.SIGTERM)",
        ]
        self.assertEqual(
            retry_on_143(
                command,
                environ={
                    "RETRY_ON_143_MAX_RETRIES": "0",
                    "RETRY_ON_143_SLEEP_SECONDS": "0",
                },
            ),
            143,
        )

    def test_custom_elan_binary_does_not_invent_another_home(self) -> None:
        from reasbook_deploy_sdk.ci import install_elan

        with tempfile.TemporaryDirectory() as temp:
            binary = Path(temp) / "custom-elan"
            binary.write_text("#!/bin/sh\nexit 0\n", encoding="utf-8")
            binary.chmod(0o755)
            selected = install_elan(
                environ={"ELAN_BIN": str(binary), "HOME": str(Path(temp) / "home")}
            )
            self.assertEqual(selected, binary.resolve())

    def test_explicit_python_is_still_version_checked(self) -> None:
        from reasbook_deploy_sdk.runtime import find_python

        with self.assertRaises(DeployExecutionError):
            find_python(requested="/bin/false")

    def test_project_runtime_uses_sdk_cache_and_toolchain_policy(self) -> None:
        from reasbook_deploy_sdk import prepare_project_runtime

        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            project = root / "repo" / "ReasBook"
            project.mkdir(parents=True)
            (project / "lean-toolchain").write_text(
                "leanprover/lean4:v4.30.0\n", encoding="utf-8"
            )
            elan_home = root / "elan"
            elan = elan_home / "bin" / "elan"
            lake = elan_home / "bin" / "lake"
            elan.parent.mkdir(parents=True)
            for executable in (elan, lake):
                executable.write_text("#!/bin/sh\nexit 0\n", encoding="utf-8")
                executable.chmod(0o755)

            cache = root / "cache"
            values = prepare_project_runtime(
                project,
                cache_root=cache,
                cache_prefix="web-",
                dry_run=True,
                environ={
                    "REASBOOK_ELAN_BIN": str(elan),
                    "REASBOOK_PYTHON_BIN": sys.executable,
                    "XDG_CACHE_HOME": str(root / "ci-xdg"),
                },
            )

            self.assertFalse(cache.exists())
            self.assertEqual(values["LAKE_BIN"], str(lake))
            self.assertEqual(values["REASBOOK_BUILD_LAKE_BIN"], str(lake))
            self.assertEqual(values["VERSO_ELAN_BIN"], str(elan))
            self.assertEqual(
                values["MATHLIB_CACHE_DIR"], str(cache / "mathlib" / "v4.30.0")
            )
            self.assertEqual(values["XDG_CACHE_HOME"], str(root / "ci-xdg"))

    def test_selected_deployment_uses_detached_worktree_and_manifest(self) -> None:
        from reasbook_deploy_sdk import DeploymentService

        class FakeReviewer:
            def __init__(self) -> None:
                self.index_calls = []
                self.catalog_calls = []

            def build_index(self, spec, *, dry_run=False):
                self.index_calls.append((spec, dry_run))
                spec.output.parent.mkdir(parents=True, exist_ok=True)
                spec.output.write_text('{"items": []}\n', encoding="utf-8")

            def regenerate_catalog(self, **kwargs):
                self.catalog_calls.append(kwargs)
                kwargs["output"].parent.mkdir(parents=True, exist_ok=True)
                kwargs["output"].write_text('{"books": []}\n', encoding="utf-8")

        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            repo = root / "repo"
            (repo / "ReasBook" / "Books" / "Demo_Book").mkdir(parents=True)
            (repo / "ReasBook" / "lakefile.lean").write_text(
                'lean_lib Demo_Book where\n  srcDir := "Books"\n', encoding="utf-8"
            )
            (repo / "ReasBook" / "lean-toolchain").write_text(
                "leanprover/lean4:v4.30.0\n", encoding="utf-8"
            )
            (repo / "ReasBook" / "Books" / "Demo_Book" / "Book.lean").write_text(
                "theorem demo : True := by trivial\n", encoding="utf-8"
            )
            subprocess.run(["git", "init", "-q", str(repo)], check=True)
            subprocess.run(["git", "-C", str(repo), "config", "user.email", "test@example.invalid"], check=True)
            subprocess.run(["git", "-C", str(repo), "config", "user.name", "Test"], check=True)
            subprocess.run(["git", "-C", str(repo), "add", "."], check=True)
            subprocess.run(["git", "-C", str(repo), "commit", "-qm", "initial"], check=True)
            subprocess.run(["git", "-C", str(repo), "branch", "v4.30.0"], check=True)
            reviewer = FakeReviewer()
            config = DeploymentConfig(
                repo_root=repo,
                reviewer_root=root / "reviewer",
                data_root=root / "data",
                cache_root=root / "cache",
                books=("Demo_Book",),
                stacks_root=None,
                build=False,
                python_bin=sys.executable,
            )
            report = DeploymentService(config, reviewer=reviewer).deploy()

            self.assertEqual(len(report.results), 1)
            self.assertEqual(report.results[0].status, "indexed")
            self.assertIsNotNone(report.manifest)
            self.assertTrue(report.manifest.is_file())
            manifest_payload = json.loads(report.manifest.read_text(encoding="utf-8"))
            self.assertEqual(manifest_payload["manifest"], str(report.manifest))
            self.assertEqual(len(reviewer.index_calls), 1)
            worktrees = list((root / "cache" / "sources").iterdir())
            self.assertEqual(len(worktrees), 1)
            self.assertTrue((worktrees[0] / ".reasbook-deploy-source.json").is_file())

    def test_dry_run_does_not_create_cache_or_start_server(self) -> None:
        from reasbook_deploy_sdk import DeploymentService

        class FakeReviewer:
            def build_index(self, spec, *, dry_run=False):
                self.dry_run = dry_run

            def regenerate_catalog(self, **kwargs):
                self.catalog_dry_run = kwargs["dry_run"]

        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            repo = root / "repo"
            (repo / "ReasBook" / "Books" / "Demo_Book").mkdir(parents=True)
            (repo / "ReasBook" / "Books" / "Demo_Book" / "Book.lean").write_text("", encoding="utf-8")
            subprocess.run(["git", "init", "-q", str(repo)], check=True)
            subprocess.run(["git", "-C", str(repo), "config", "user.email", "test@example.invalid"], check=True)
            subprocess.run(["git", "-C", str(repo), "config", "user.name", "Test"], check=True)
            subprocess.run(["git", "-C", str(repo), "add", "."], check=True)
            subprocess.run(["git", "-C", str(repo), "commit", "-qm", "initial"], check=True)
            subprocess.run(["git", "-C", str(repo), "branch", "v4.30.0"], check=True)
            cache = root / "cache"
            service = DeploymentService(
                DeploymentConfig(
                    repo_root=repo,
                    reviewer_root=root / "reviewer",
                    data_root=root / "data",
                    cache_root=cache,
                    books=("Demo_Book",),
                    stacks_root=None,
                    build=True,
                    dry_run=True,
                    serve=True,
                    python_bin=sys.executable,
                ),
                reviewer=FakeReviewer(),
            )
            service.deploy()
            self.assertFalse(cache.exists())

    def test_pipeline_stops_at_failed_stage_and_preserves_order(self) -> None:
        from reasbook_deploy_sdk import CallableStage, DeploymentPipeline

        calls: list[str] = []

        def first(dry_run: bool):
            calls.append(f"first:{dry_run}")
            return {"ok": True}

        def failed(dry_run: bool):
            calls.append(f"failed:{dry_run}")
            raise RuntimeError("stage failed")

        pipeline = DeploymentPipeline(
            (
                CallableStage("build", first),
                CallableStage("verso", failed),
                CallableStage("graph", first),
            )
        )
        results = pipeline.run()
        self.assertEqual(calls, ["first:False", "failed:False"])
        self.assertEqual([item.status for item in results], ["success", "failed"])

    def test_stage_result_serializes_path_and_unknown_values(self) -> None:
        from reasbook_deploy_sdk import StageResult

        payload = StageResult("custom", "success", value={"path": Path("/tmp/x"), "obj": object()}).public_dict()
        self.assertEqual(payload["value"]["path"], "/tmp/x")
        self.assertIsInstance(payload["value"]["obj"], str)

    def test_file_transaction_restores_existing_and_removes_new_files(self) -> None:
        from reasbook_deploy_sdk.transaction import FileTransaction

        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            existing = root / "existing.json"
            created = root / "created.json"
            existing.write_text("old", encoding="utf-8")
            try:
                with FileTransaction(root / "tx") as transaction:
                    transaction.watch(existing)
                    transaction.watch(created)
                    existing.write_text("new", encoding="utf-8")
                    created.write_text("new", encoding="utf-8")
                    raise RuntimeError("abort")
            except RuntimeError:
                pass
            self.assertEqual(existing.read_text(encoding="utf-8"), "old")
            self.assertFalse(created.exists())

    def test_docker_deployment_dry_run_has_no_external_requirements(self) -> None:
        from reasbook_deploy_sdk import DockerDeploymentConfig, deploy_static

        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            deploy_static(
                DockerDeploymentConfig(
                    repo_root=root,
                    compose_file=root / "docker-compose.yml",
                    site_root=root / "ReasBookWeb" / "_site",
                    dry_run=True,
                )
            )

    def test_docker_deployment_requires_skip_build_for_custom_site(self) -> None:
        from reasbook_deploy_sdk import DockerDeploymentConfig

        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            with self.assertRaisesRegex(
                DeployConfigError,
                "custom Docker site directory requires --skip-build",
            ):
                DockerDeploymentConfig(
                    repo_root=root,
                    compose_file=root / "docker-compose.yml",
                    site_root=root / "external-site",
                ).resolved()

    def test_docker_deployment_accepts_packaged_site_read_only(self) -> None:
        from reasbook_deploy_sdk import DockerDeploymentConfig

        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            resolved = DockerDeploymentConfig(
                repo_root=root,
                compose_file=root / "docker-compose.yml",
                site_root=root / "release" / "site",
                skip_build=True,
            ).resolved()
            self.assertEqual(resolved.site_root, (root / "release" / "site").resolve())

    def test_docker_deployment_probes_the_served_site_prefix(self) -> None:
        from reasbook_deploy_sdk import DockerDeploymentConfig, deploy_static
        from reasbook_sdk_common import CommandResult

        class FakeRunner:
            def run(self, command):
                return CommandResult(argv=command.argv, returncode=0)

        class HealthyResponse:
            status = 200

            def __enter__(self):
                return self

            def __exit__(self, *_args):
                return False

        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            compose = root / "docker-compose.yml"
            site = root / "ReasBookWeb" / "_site"
            site.mkdir(parents=True)
            (site / "index.html").write_text("site", encoding="utf-8")
            compose.write_text("services: {}\n", encoding="utf-8")
            with patch(
                "reasbook_deploy_sdk.docker.urlopen",
                return_value=HealthyResponse(),
            ) as probe:
                deploy_static(
                    DockerDeploymentConfig(
                        repo_root=root,
                        compose_file=compose,
                        site_root=site,
                        skip_build=True,
                    ),
                    runner=FakeRunner(),
                )

            probe.assert_called_once_with(
                "http://127.0.0.1:3200/ReasBook/",
                timeout=1.0,
            )

    def test_docker_port_validation(self) -> None:
        from reasbook_deploy_sdk import DockerDeploymentConfig

        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            with self.assertRaises(DeployConfigError):
                DockerDeploymentConfig(
                    repo_root=root,
                    compose_file=root / "compose.yml",
                    site_root=root / "ReasBookWeb" / "_site",
                    port=0,
                ).resolved()


if __name__ == "__main__":
    unittest.main()
