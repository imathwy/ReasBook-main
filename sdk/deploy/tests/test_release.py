from __future__ import annotations

from datetime import datetime, timezone
import json
import hashlib
from pathlib import Path
import shutil
import subprocess
import tempfile
import unittest
from unittest.mock import patch

from reasbook_sdk_common import CommandResult
from reasbook_deploy_sdk import DeployConfigError, DeployExecutionError
from reasbook_deploy_sdk.release.build_plan import (
    BranchPlanFactory,
    ReleaseBuildOptions,
)
from reasbook_deploy_sdk.release.bundle import (
    BundleVerifier,
    ReleaseBundler,
    _ArchiveMember,
)
from reasbook_deploy_sdk.release.cli import build_parser
from reasbook_deploy_sdk.release.artifacts import (
    PagesSiteProjector,
    artifact_policy_digest,
    create_release_set,
)
from reasbook_deploy_sdk.release.config import (
    dump_profile_snapshot,
    load_canonical_projects,
    load_profile,
    load_registry,
)
from reasbook_deploy_sdk.release.models import (
    CanonicalProjects,
    DeploymentProfile,
    GitHubPublishProfile,
    ProjectSpec,
    ReleaseArtifactPolicy,
    RegistryBranch,
    ReleasePolicy,
    ReleaseSpec,
    SourceProject,
    ToolchainRegistry,
)
from reasbook_deploy_sdk.release.planner import ReleasePlanner
from reasbook_deploy_sdk.release.github import GitHubReleasePublisher
from reasbook_deploy_sdk.release.pages_config import GitHubPagesConfigurator
from reasbook_deploy_sdk.release.results import (
    BranchBuildResult,
    BundleInfo,
    ReleaseBuildReport,
    ReleasePackageResult,
    StageOutcome,
)
from reasbook_deploy_sdk.release.site import ReleaseSiteAssembler
from reasbook_deploy_sdk.release.service import (
    ReleaseContext,
    StaticReleaseService,
)
from reasbook_deploy_sdk.release.self_hosted import SelfHostedInstaller
from reasbook_deploy_sdk.release.source import _credential_free_remote
from reasbook_deploy_sdk.release.store import ReleaseLayout, ReleaseStore
from reasbook_deploy_sdk.release.tooling import (
    TOOLING_SNAPSHOT_ENTRIES,
    bind_tooling_revision,
    snapshot_ignore_for,
    tooling_digest_from_revision,
    tooling_source_digest,
)


REPO_ROOT = Path(__file__).resolve().parents[3]


def release_manifest_fixture(
    release_id: str,
    *,
    artifact: str = "full",
    spec_digest: str | None = None,
    site_digest: str | None = None,
    file_count: int = 1,
    total_bytes: int = 7,
) -> dict:
    value = {
        "schema_version": 2,
        "release_id": release_id,
        "spec_digest": spec_digest or "sha256:" + "a" * 64,
        "artifact": artifact,
        "status": "success",
        "base_path": "/ReasBook/",
        "generated_at": "2026-09-01T14:00:00Z",
        "site_tree_sha256": site_digest or "sha256:" + "b" * 64,
        "file_count": file_count,
        "total_bytes": total_bytes,
        "projects": [],
        "branches": [],
    }
    return value


def github_pages_bundle_fixture(
    root: Path,
    release_id: str,
) -> tuple[BundleInfo, list[Path]]:
    """Create the four canonical, mutually bound Pages release assets."""

    spec_digest = "sha256:" + release_id.rsplit("-", 1)[-1] + "a" * 52
    site_digest = "sha256:" + "b" * 64
    bundle_path = root / f"{release_id}.pages.site.tar.zst"
    bundle_path.write_text("fixture", encoding="utf-8")
    digest = hashlib.sha256(bundle_path.read_bytes()).hexdigest()
    manifest_path = root / "release-manifest.json"
    manifest_path.write_text(
        json.dumps(
            release_manifest_fixture(
                release_id,
                artifact="pages",
                spec_digest=spec_digest,
                site_digest=site_digest,
            )
        ),
        encoding="utf-8",
    )
    checksums_path = root / "SHA256SUMS"
    checksums_path.write_text(
        f"{digest}  {bundle_path.name}\n",
        encoding="utf-8",
    )
    release_set_path = root / "release-set.json"
    release_set_path.write_text(
        json.dumps(
            {
                "schema_version": 1,
                "release_id": release_id,
                "spec_digest": spec_digest,
                "generated_at": "2026-09-01T14:00:00Z",
                "artifact_policy_sha256": "sha256:" + "c" * 64,
                "artifacts": [
                    {
                        "name": "full",
                        "bundle": f"{release_id}.site.tar.zst",
                        "bundle_sha256": "sha256:" + "d" * 64,
                        "site_tree_sha256": "sha256:" + "e" * 64,
                        "file_count": 2,
                        "total_bytes": 8,
                    },
                    {
                        "name": "pages",
                        "bundle": bundle_path.name,
                        "bundle_sha256": "sha256:" + digest,
                        "site_tree_sha256": site_digest,
                        "file_count": 1,
                        "total_bytes": 7,
                    },
                ],
            }
        ),
        encoding="utf-8",
    )
    assets = [bundle_path, manifest_path, checksums_path, release_set_path]
    return (
        BundleInfo(
            release_id,
            str(bundle_path),
            str(manifest_path),
            str(checksums_path),
            "sha256:" + digest,
            artifact="pages",
            release_set=str(release_set_path),
        ),
        assets,
    )


class FakeReleaseSource:
    def __init__(self) -> None:
        self.commits = {
            "v4.26.0": "a" * 40,
            "v4.30.0": "b" * 40,
        }
        self.projects = {
            "v4.26.0": (
                SourceProject("books", "Demo"),
                SourceProject("papers", "OnlyOld"),
            ),
            "v4.30.0": (SourceProject("books", "Demo"),),
        }
        self.fetch_count = 0

    def fetch(self) -> None:
        self.fetch_count += 1

    def repository_url(self) -> str:
        return "https://github.com/acme/reasbook.git"

    def registry_commit(self) -> str:
        return "c" * 40

    def tooling_revision(self) -> str:
        return "c" * 40

    def branch_commit(self, branch: str) -> str:
        return self.commits[branch]

    def read_text(self, branch: str, path: str) -> str:
        if path.endswith("lean-toolchain"):
            return f"leanprover/lean4:{branch}"
        if path.endswith("lake-manifest.json"):
            return json.dumps({"version": branch})
        if branch == "v4.26.0":
            return "lean_lib Books where\n\nlean_lib Papers where\n"
        return 'lean_lib Demo where\n  srcDir := "Books"\n'

    def discover_projects(self, branch: str):
        return self.projects[branch]


class RootedReleaseSource(FakeReleaseSource):
    """Minimal v4.32-style source with an explicit Lake root module."""

    def __init__(self) -> None:
        super().__init__()
        self.commits["v4.32.2"] = "d" * 40
        self.projects["v4.32.2"] = (SourceProject("papers", "TR_LALM_theory"),)

    def read_text(self, branch: str, path: str) -> str:
        if branch == "v4.32.2" and path.endswith("lakefile.lean"):
            return (
                "lean_lib TR_LALM_theory where\n"
                '  srcDir := "Papers"\n'
                "  roots := #[`TR_LALM_theory]\n"
            )
        return super().read_text(branch, path)


def profile(root: Path, *, historical: bool = True) -> DeploymentProfile:
    return DeploymentProfile(
        name="github-pages",
        registry=root / "toolchains.yml",
        canonical_projects=root / "canonical.yml",
        base_path="/ReasBook/",
        include_historical_versions=historical,
        policy=ReleasePolicy(),
        publish=GitHubPublishProfile(repository="acme/reasbook"),
    )


class ReleasePlanningTests(unittest.TestCase):
    def setUp(self) -> None:
        self.registry = ToolchainRegistry(
            (
                RegistryBranch("v4.26.0", "v4.26.0", "active"),
                RegistryBranch("v4.30.0", "v4.30.0", "active"),
                RegistryBranch("v4.32.0", "v4.32.0", "empty"),
            )
        )
        self.now = datetime(2026, 9, 1, 14, 0, tzinfo=timezone.utc)

    def test_explicit_canonical_produces_deterministic_immutable_spec(self) -> None:
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            planner = ReleasePlanner(FakeReleaseSource(), resolved_at=self.now)
            canonical = CanonicalProjects((("books/Demo", "v4.30.0"),))
            first = planner.resolve(profile(root), self.registry, canonical)
            second = planner.resolve(profile(root), self.registry, canonical)

            self.assertEqual(first.spec_digest, second.spec_digest)
            self.assertEqual(first.release_id, second.release_id)
            self.assertEqual(len(first.projects), 3)
            demo = [
                item
                for item in first.projects
                if item.key == "books/Demo" and item.canonical
            ]
            self.assertEqual([item.branch for item in demo], ["v4.30.0"])
            self.assertEqual(
                ReleaseSpec.from_dict(first.public_dict()),
                first,
            )

    def test_deployment_profile_rejects_unimplemented_artifact_projection(self) -> None:
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            with self.assertRaisesRegex(DeployConfigError, "pages artifact"):
                DeploymentProfile(
                    name="github-pages",
                    registry=root / "toolchains.yml",
                    canonical_projects=root / "canonical.yml",
                    base_path="/ReasBook/",
                    include_historical_versions=True,
                    policy=ReleasePolicy(),
                    publish=GitHubPublishProfile(repository="acme/reasbook"),
                    artifacts=(
                        profile(root).artifact("full"),
                        ReleaseArtifactPolicy(
                            name="pages",
                            history_mode="full",
                            dependency_docs="full",
                            max_site_files=60_000,
                            max_site_bytes=850_000_000,
                            max_bundle_bytes=950_000_000,
                        ),
                    ),
                )

    def test_pages_projection_rejects_encoded_parent_path(self) -> None:
        with tempfile.TemporaryDirectory() as temp:
            pages = Path(temp) / "pages"
            pages.mkdir()
            with self.assertRaisesRegex(DeployExecutionError, "unsafe internal"):
                PagesSiteProjector._resolve_missing_reference(
                    "https://reasbook.invalid",
                    "/ReasBook/",
                    "https://reasbook.invalid/ReasBook/index.html",
                    "/ReasBook/%2e%2e/private.txt",
                    pages,
                )

    def test_release_cli_exposes_portable_self_hosted_install(self) -> None:
        parsed = build_parser().parse_args(
            [
                "install",
                "/transfer/release.site.tar.zst",
                "--sha256",
                "a" * 64,
                "--release-set",
                "/transfer/release-set.json",
                "--artifact-policy-sha256",
                "b" * 64,
                "--deploy-root",
                "/srv/reasbook",
                "--filesystem-health-only",
            ]
        )
        self.assertEqual(parsed.release_command, "install")
        self.assertEqual(parsed.deploy_root, Path("/srv/reasbook"))

        with self.assertRaises(SystemExit):
            build_parser().parse_args(
                [
                    "install",
                    "/transfer/release.site.tar.zst",
                    "--sha256",
                    "a" * 64,
                    "--release-set",
                    "/transfer/release-set.json",
                    "--deploy-root",
                    "/srv/reasbook",
                    "--filesystem-health-only",
                ]
            )
        with self.assertRaises(SystemExit):
            build_parser().parse_args(
                [
                    "install",
                    "/transfer/release.site.tar.zst",
                    "--sha256",
                    "",
                    "--release-set",
                    "/transfer/release-set.json",
                    "--artifact-policy-sha256",
                    "b" * 64,
                    "--deploy-root",
                    "/srv/reasbook",
                    "--filesystem-health-only",
                ]
            )
        with self.assertRaises(SystemExit):
            build_parser().parse_args(
                [
                    "install",
                    "/transfer/release.site.tar.zst",
                    "--sha256",
                    "a" * 64,
                    "--release-set",
                    "/transfer/release-set.json",
                    "--artifact-policy-sha256",
                    "b" * 64,
                    "--deploy-root",
                    "/srv/reasbook",
                ]
            )

        build = build_parser().parse_args(
            ["build", "site-20260901T140000Z-" + "a" * 12]
        )
        self.assertEqual(build.max_parallel_branches, 3)
        self.assertEqual(build.docs_timeout_seconds, 43200.0)

        configured = build_parser().parse_args(
            ["configure-pages", "--profile", "github-pages", "--dry-run"]
        )
        self.assertEqual(configured.release_command, "configure-pages")
        self.assertTrue(configured.dry_run)

        with self.assertRaisesRegex(DeployConfigError, "plain YAML"):
            GitHubPublishProfile(
                repository="acme/reasbook",
                workflow="../untrusted.yml",
            )

    def test_repository_identity_strips_embedded_credentials(self) -> None:
        self.assertEqual(
            _credential_free_remote("https://token@example.invalid/acme/reasbook.git"),
            "https://example.invalid/acme/reasbook.git",
        )

    def test_tooling_revision_is_deterministically_bound_to_tree_digest(self) -> None:
        digest = "d" * 64
        revision = bind_tooling_revision("abc+dirty:fingerprint", digest)

        self.assertEqual(tooling_digest_from_revision(revision), digest)
        self.assertEqual(
            revision,
            "abc+dirty:fingerprint+tooling-sha256:" + digest,
        )
        with self.assertRaisesRegex(DeployConfigError, "already bound"):
            bind_tooling_revision(revision, digest)

    def test_tooling_snapshot_ignores_sdk_packaging_outputs_by_path(self) -> None:
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp) / "repo"
            for sequence, relative in enumerate(TOOLING_SNAPSHOT_ENTRIES):
                directory = root / relative
                directory.mkdir(parents=True, exist_ok=True)
                (directory / f"source-{sequence}.txt").write_text(
                    f"source {sequence}\n", encoding="utf-8"
                )
            capability_source = (
                root / "sdk" / "build" / "src" / "reasbook_build_sdk" / "core.py"
            )
            capability_source.parent.mkdir(parents=True)
            capability_source.write_text("VALUE = 1\n", encoding="utf-8")
            clean_digest = tooling_source_digest(root)

            generated = (
                root / "sdk" / "build" / "build" / "lib" / "stale.py",
                root / "sdk" / "build" / "dist" / "stale.whl",
                root
                / "sdk"
                / "build"
                / "src"
                / "reasbook_build_sdk.egg-info"
                / "PKG-INFO",
                root / "sdk" / "deploy" / "build" / "lib" / "stale.py",
            )
            for path in generated:
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_text(f"generated: {path.name}\n", encoding="utf-8")

            self.assertEqual(tooling_source_digest(root), clean_digest)
            copied = Path(temp) / "copied"
            shutil.copytree(
                root / "sdk",
                copied / "sdk",
                ignore=snapshot_ignore_for(root),
            )
            self.assertTrue(
                (copied / capability_source.relative_to(root)).is_file()
            )
            for path in generated:
                self.assertFalse((copied / path.relative_to(root)).exists())

    def test_duplicate_project_without_canonical_is_rejected(self) -> None:
        with tempfile.TemporaryDirectory() as temp:
            planner = ReleasePlanner(FakeReleaseSource(), resolved_at=self.now)
            with self.assertRaisesRegex(
                DeployConfigError, "needs an explicit canonical"
            ):
                planner.resolve(
                    profile(Path(temp)),
                    self.registry,
                    CanonicalProjects(()),
                )

    def test_explicit_lake_root_is_used_for_release_target(self) -> None:
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            source = RootedReleaseSource()
            registry = ToolchainRegistry(
                (RegistryBranch("v4.32.2", "v4.32.2", "active"),)
            )
            spec = ReleasePlanner(source, resolved_at=self.now).resolve(
                profile(root), registry, CanonicalProjects(())
            )
            self.assertEqual(spec.projects[0].build_target, "TR_LALM_theory")

    def test_historical_versions_can_be_omitted(self) -> None:
        with tempfile.TemporaryDirectory() as temp:
            planner = ReleasePlanner(FakeReleaseSource(), resolved_at=self.now)
            spec = planner.resolve(
                profile(Path(temp), historical=False),
                self.registry,
                CanonicalProjects((("books/Demo", "v4.30.0"),)),
            )
            self.assertEqual(
                [(item.key, item.branch) for item in spec.projects],
                [
                    ("books/Demo", "v4.30.0"),
                    ("papers/OnlyOld", "v4.26.0"),
                ],
            )

    def test_canonical_replacement_accepts_explicit_root_doc_file(self) -> None:
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            project = ProjectSpec(
                key="papers/TR_LALM_theory",
                kind="papers",
                project_id="TR_LALM_theory",
                slug="tr_lalm_theory",
                branch="v4.32.2",
                commit="d" * 40,
                source_path="ReasBook/Papers/TR_LALM_theory",
                build_target="TR_LALM_theory",
                canonical=True,
                outputs=ReleasePolicy().outputs(),
            )
            monolith = root / "monolith"
            branch_site = root / "branch-site"
            source = branch_site / "docs" / "ReasBook" / "TR_LALM_theory.html"
            source.parent.mkdir(parents=True)
            source.write_text("root-doc", encoding="utf-8")

            ReleaseSiteAssembler._replace_canonical_project(
                monolith, branch_site, project
            )

            target = monolith / "docs" / "ReasBook" / "TR_LALM_theory.html"
            self.assertEqual(target.read_text(encoding="utf-8"), "root-doc")

    def test_site_publish_replaces_symlink_and_restores_on_rename_failure(self) -> None:
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            layout = ReleaseLayout(root / "cache", "site-20260901T140000Z-" + "a" * 12)
            assembler = ReleaseSiteAssembler(root, layout)
            layout.root.mkdir(parents=True)
            old = root / "old-site"
            old.mkdir()
            (old / "index.html").write_text("<html>old</html>", encoding="utf-8")
            layout.site.parent.mkdir(parents=True, exist_ok=True)
            layout.site.symlink_to(old, target_is_directory=True)

            staged = root / "staged"
            staged.mkdir()
            (staged / "index.html").write_text("<html>new</html>", encoding="utf-8")
            assembler._publish(staged)

            self.assertFalse(layout.site.is_symlink())
            self.assertEqual(
                (layout.site / "index.html").read_text(encoding="utf-8"),
                "<html>new</html>",
            )
            self.assertTrue(old.is_dir())

            # A failed second rename must put the original symlink back.
            shutil.rmtree(layout.site)
            layout.site.symlink_to(old, target_is_directory=True)
            staged = root / "staged-failure"
            staged.mkdir()
            (staged / "index.html").write_text("<html>failed</html>", encoding="utf-8")
            import reasbook_deploy_sdk.release.site as site_module

            real_replace = site_module.os.replace

            def fail_staged(source, destination):
                if Path(source) == staged:
                    raise OSError("injected rename failure")
                return real_replace(source, destination)

            with patch.object(site_module.os, "replace", side_effect=fail_staged):
                with self.assertRaises(OSError):
                    assembler._publish(staged)
            self.assertTrue(layout.site.is_symlink())
            self.assertEqual(layout.site.resolve(), old.resolve())

    def test_profile_registry_and_canonical_yaml_are_strictly_loaded(self) -> None:
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            config = root / "config"
            config.mkdir()
            (config / "toolchains.yml").write_text(
                "schema_version: 1\n"
                "branches:\n"
                "  - version: v4.30.0\n"
                "    branch: v4.30.0\n"
                "    status: active\n",
                encoding="utf-8",
            )
            (config / "canonical.yml").write_text(
                "schema_version: 1\n" "books:\n" "  Demo: v4.30.0\n" "papers: {}\n",
                encoding="utf-8",
            )
            profile_path = config / "github-pages.yml"
            profile_path.write_text(
                "schema_version: 1\n"
                "name: github-pages\n"
                "registry: config/toolchains.yml\n"
                "canonical_projects: config/canonical.yml\n"
                "selection:\n"
                "  mode: all_active\n"
                "  exclude: [books/Broken]\n"
                "site:\n"
                "  base_path: /ReasBook/\n"
                "  include_historical_versions: true\n"
                "policy:\n"
                "  theorem_graph: compiled_or_source\n"
                "publish:\n"
                "  adapter: github_pages\n"
                "  repository: acme/reasbook\n",
                encoding="utf-8",
            )

            loaded = load_profile(profile_path, repo_root=root)
            self.assertEqual(loaded.exclude, ("books/Broken",))
            self.assertEqual(len(load_registry(loaded.registry).active()), 1)
            self.assertEqual(
                load_canonical_projects(loaded.canonical_projects).get("books/Demo"),
                "v4.30.0",
            )
            snapshot = root / "snapshot"
            snapshot.mkdir()
            (snapshot / "profile.yml").write_text(
                dump_profile_snapshot(loaded), encoding="utf-8"
            )
            (snapshot / "toolchains.yml").write_text(
                (config / "toolchains.yml").read_text(encoding="utf-8"),
                encoding="utf-8",
            )
            (snapshot / "canonical-projects.yml").write_text(
                (config / "canonical.yml").read_text(encoding="utf-8"),
                encoding="utf-8",
            )
            restored = load_profile(snapshot / "profile.yml", repo_root=snapshot)
            self.assertEqual(restored.publish, loaded.publish)

    def _spec(self, root: Path):
        return ReleasePlanner(FakeReleaseSource(), resolved_at=self.now).resolve(
            profile(root),
            self.registry,
            CanonicalProjects((("books/Demo", "v4.30.0"),)),
        )

    def _self_hosted_package(
        self,
        root: Path,
        *,
        generated_at: datetime | None = None,
        content: str = "site",
    ):
        at = generated_at or self.now
        spec = ReleasePlanner(FakeReleaseSource(), resolved_at=at).resolve(
            profile(root),
            self.registry,
            CanonicalProjects((("books/Demo", "v4.30.0"),)),
        )
        layout = ReleaseLayout(root / "cache", spec.release_id)
        store = ReleaseStore(layout)
        store.initialize(spec)
        layout.site.mkdir()
        (layout.site / "index.html").write_text(content, encoding="utf-8")
        (layout.site / "release-spec.json").write_text(
            json.dumps(spec.public_dict()),
            encoding="utf-8",
        )
        report = ReleaseBuildReport.from_branches(
            spec,
            tuple(
                BranchBuildResult(
                    branch.name,
                    branch.commit,
                    "success",
                    str(root / branch.name),
                    (StageOutcome("fixture", "success"),),
                )
                for branch in spec.branches
            ),
        )
        bundler = ReleaseBundler(layout, store, generated_at=at)
        full = bundler.package(spec, report)
        shutil.copytree(layout.site, layout.pages_site)
        pages = bundler.package_pages(
            spec,
            report,
            policy=profile(root).artifact("pages"),
        )
        _release_set, bundles = create_release_set(
            layout,
            store,
            spec,
            profile(root).artifacts,
            (full, pages),
        )
        full = next(item for item in bundles if item.artifact == "full")
        return spec, full, layout.release_set, layout

    @staticmethod
    def _write_raw_bundle(package_root: Path, bundle: Path, *extra: str) -> None:
        subprocess.run(
            (
                "tar",
                "--zstd",
                "-cf",
                str(bundle),
                *extra,
                "-C",
                str(package_root),
                "site",
                "release-manifest.json",
            ),
            check=True,
            capture_output=True,
            text=True,
        )

    def test_branch_plan_is_ordered_and_uses_isolated_runtime_cache(self) -> None:
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            spec = self._spec(root)
            layout = ReleaseLayout(root / "cache", spec.release_id)
            branch = spec.branch("v4.26.0")
            worktree = root / "worktree"
            worktree.mkdir()
            plan = BranchPlanFactory(
                REPO_ROOT,
                root / "cache",
                layout,
                ReleaseBuildOptions(),
            ).create(spec, branch, worktree)

            self.assertEqual(
                [step.name for step in plan.steps],
                [
                    "cache",
                    "lean",
                    "docs",
                    "verso",
                    "publish-docs",
                    "theorem-graph",
                ],
            )
            environment = dict(plan.steps[0].env)
            self.assertIn(
                spec.branch("v4.26.0").commit[:12],
                environment["REASBOOK_RUNTIME_CACHE_PREFIX"],
            )
            self.assertEqual(
                environment["REASBOOK_SITE_ROOT"],
                "/ReasBook/versions/v4.26.0/",
            )
            self.assertEqual(
                environment["REASBOOK_DOC_SOURCE"],
                environment["REASBOOK_DOC_BUILD_DIR"] + "/doc",
            )
            self.assertIn("Demo.Book", environment["REASBOOK_LAKE_TARGETS"])

    def test_release_store_and_bundle_round_trip(self) -> None:
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            spec = self._spec(root)
            layout = ReleaseLayout(root / "cache", spec.release_id)
            store = ReleaseStore(layout)
            store.initialize(spec)
            with self.assertRaisesRegex(DeployExecutionError, "another release"):
                store.write_build_report(
                    ReleaseBuildReport(
                        "site-20260901T140000Z-" + "0" * 12,
                        spec.spec_digest,
                        "success",
                        (),
                    )
                )
            branch_sites = {
                "v4.26.0": root / "site-426",
                "v4.30.0": root / "site-430",
            }
            self._write_branch_site(
                branch_sites["v4.26.0"],
                books={"Demo": "old"},
                papers={"OnlyOld": "paper"},
            )
            self._write_branch_site(
                branch_sites["v4.30.0"],
                books={"Demo": "canonical"},
                papers={},
            )
            report = ReleaseBuildReport.from_branches(
                spec,
                tuple(
                    BranchBuildResult(
                        branch.name,
                        branch.commit,
                        "success",
                        str(branch_sites[branch.name]),
                        (StageOutcome("fixture", "success"),),
                    )
                    for branch in spec.branches
                ),
            )
            store.write_build_report(report)
            ReleaseSiteAssembler(REPO_ROOT, layout).assemble(spec, report)
            store.transition("validated", completed_stage="site")

            canonical_doc = layout.site / "sites" / "demo" / "docs" / "Book.html"
            canonical_redirect = canonical_doc.read_text(encoding="utf-8")
            self.assertIn('http-equiv="refresh"', canonical_redirect)
            self.assertIn(
                "docs/ReasBook/Books/Demo/Book.html",
                canonical_redirect,
            )
            self.assertEqual(
                (
                    layout.site
                    / "versions"
                    / "v4.30.0"
                    / "docs"
                    / "ReasBook"
                    / "Books"
                    / "Demo"
                    / "Book.html"
                ).read_text(encoding="utf-8"),
                "<!doctype html><html><body>canonical</body></html>",
            )
            self.assertTrue(
                (layout.site / "versions" / "v4.26.0" / "index.html").is_file()
            )
            self.assertIn(
                "Version Archive",
                (layout.site / "index.html").read_text(encoding="utf-8"),
            )
            bundler = ReleaseBundler(
                layout,
                store,
                generated_at=self.now,
            )
            bundle = bundler.package(spec, report)
            repeated = bundler.package(spec, report)
            self.assertEqual(bundle.bundle_sha256, repeated.bundle_sha256)
            with self.assertRaisesRegex(DeployConfigError, "SHA-256"):
                BundleVerifier().inspect(
                    Path(bundle.bundle),
                    expected_sha256="",
                )
            self.assertNotIn(
                str(root),
                layout.manifest.read_text(encoding="utf-8"),
            )
            extracted = root / "extracted"
            manifest = BundleVerifier().verify(
                Path(bundle.bundle),
                expected_sha256=bundle.bundle_sha256,
                extract_to=extracted,
            )
            self.assertEqual(manifest.release_id, spec.release_id)
            self.assertTrue((extracted / "index.html").is_file())
            self.assertEqual(
                ReleaseStore.find_by_digest(root / "cache", spec.spec_digest),
                spec,
            )

    def test_release_set_packages_slim_pages_and_installable_full_site(self) -> None:
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            spec = self._spec(root)
            layout = ReleaseLayout(root / "cache", spec.release_id)
            store = ReleaseStore(layout)
            store.initialize(spec)
            branch_sites = {
                "v4.26.0": root / "site-426",
                "v4.30.0": root / "site-430",
            }
            self._write_branch_site(
                branch_sites["v4.26.0"],
                books={"Demo": "old"},
                papers={"OnlyOld": "paper"},
            )
            self._write_branch_site(
                branch_sites["v4.30.0"],
                books={"Demo": "canonical"},
                papers={},
            )
            dependency = (
                branch_sites["v4.30.0"]
                / "docs"
                / "ReasBook"
                / "Mathlib"
                / "Heavy.html"
            )
            dependency.parent.mkdir(parents=True)
            dependency.write_text("x" * 200_000, encoding="utf-8")
            refreshed_dependency = dependency.with_name("RefreshTarget.html")
            refreshed_dependency.write_text("refresh target", encoding="utf-8")
            project_doc = (
                branch_sites["v4.30.0"]
                / "docs"
                / "ReasBook"
                / "Books"
                / "Demo"
                / "Book.html"
            )
            project_doc.write_text(
                '<!doctype html><html><head><meta http-equiv="refresh" '
                'content="0; url=../../Mathlib/RefreshTarget.html"></head>'
                '<body><a href="../../Mathlib/Heavy.html">'
                "Dependency</a></body></html>",
                encoding="utf-8",
            )
            report = ReleaseBuildReport.from_branches(
                spec,
                tuple(
                    BranchBuildResult(
                        branch.name,
                        branch.commit,
                        "success",
                        str(branch_sites[branch.name]),
                        (StageOutcome("fixture", "success"),),
                    )
                    for branch in spec.branches
                ),
            )
            store.write_build_report(report)
            ReleaseSiteAssembler(REPO_ROOT, layout).assemble(spec, report)
            store.transition("validated", completed_stage="site")

            PagesSiteProjector().project(spec, layout.site, layout.pages_site)
            stub = (
                layout.pages_site
                / "versions"
                / "v4.30.0"
                / "docs"
                / "ReasBook"
                / "Mathlib"
                / "Heavy.html"
            )
            self.assertIn(
                "not included in the bounded Pages artifact",
                stub.read_text(encoding="utf-8"),
            )
            self.assertLess(stub.stat().st_size, dependency.stat().st_size)
            self.assertIn(
                "not included in the bounded Pages artifact",
                stub.with_name("RefreshTarget.html").read_text(encoding="utf-8"),
            )
            self.assertFalse(
                (
                    layout.pages_site
                    / "versions"
                    / "v4.26.0"
                    / "books"
                    / "demo"
                ).exists()
            )

            bundler = ReleaseBundler(layout, store, generated_at=self.now)
            full = bundler.package(
                spec,
                report,
                policy=profile(root).artifact("full"),
            )
            pages = bundler.package_pages(
                spec,
                report,
                policy=profile(root).artifact("pages"),
            )
            release_set, bundles = create_release_set(
                layout,
                store,
                spec,
                profile(root).artifacts,
                (full, pages),
            )
            pages = next(item for item in bundles if item.artifact == "pages")
            full = next(item for item in bundles if item.artifact == "full")
            package = ReleasePackageResult(full, pages, release_set)
            self.assertEqual(
                release_set.artifact("pages").bundle,
                Path(pages.bundle).name,
            )
            self.assertEqual(
                set(package.public_dict()["artifacts"]),
                {"full", "pages"},
            )
            self.assertEqual(
                BundleVerifier().verify(
                    Path(pages.bundle), expected_sha256=pages.bundle_sha256
                ).artifact,
                "pages",
            )

            deployment = SelfHostedInstaller(root / "server").install(
                Path(full.bundle),
                release_set=layout.release_set,
                expected_sha256=full.bundle_sha256,
                expected_artifact_policy_sha256=artifact_policy_digest(
                    profile(root).artifacts
                ),
                filesystem_health_only=True,
            )
            current = root / "server" / "current"
            self.assertTrue(current.is_symlink())
            self.assertEqual(
                (current / "public" / "ReasBook" / "index.html").read_text(
                    encoding="utf-8"
                ),
                (layout.site / "index.html").read_text(encoding="utf-8"),
            )
            self.assertEqual(deployment.release_id, spec.release_id)

    def test_self_hosted_install_rejects_pages_artifact_as_full(self) -> None:
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            spec = self._spec(root)
            layout = ReleaseLayout(root / "cache", spec.release_id)
            store = ReleaseStore(layout)
            store.initialize(spec)
            layout.pages_site.mkdir(parents=True)
            (layout.pages_site / "index.html").write_text("site", encoding="utf-8")
            (layout.pages_site / "release-spec.json").write_text(
                json.dumps(spec.public_dict()), encoding="utf-8"
            )
            report = ReleaseBuildReport.from_branches(
                spec,
                tuple(
                    BranchBuildResult(
                        branch.name,
                        branch.commit,
                        "success",
                        str(root / branch.name),
                        (StageOutcome("fixture", "success"),),
                    )
                    for branch in spec.branches
                ),
            )
            pages = ReleaseBundler(layout, store, generated_at=self.now).package_pages(
                spec,
                report,
                policy=profile(root).artifact("pages"),
            )
            with self.assertRaisesRegex(DeployExecutionError, "contains pages"):
                SelfHostedInstaller(root / "server").install(
                    Path(pages.bundle),
                    release_set=layout.release_set,
                    expected_artifact_policy_sha256=artifact_policy_digest(
                        profile(root).artifacts
                    ),
                    filesystem_health_only=True,
                )

    def test_bundle_preflight_rejects_unsafe_members_and_size_bombs(self) -> None:
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            _spec, full, _release_set, layout = self._self_hosted_package(root)
            archive = Path(full.bundle)

            with self.assertRaisesRegex(DeployExecutionError, "site-byte"):
                BundleVerifier(max_site_bytes=1).inspect(
                    archive,
                    expected_sha256=full.bundle_sha256,
                )

            traversal = root / "traversal.tar.zst"
            self._write_raw_bundle(
                layout.root,
                traversal,
                "--transform=s|^site/index.html$|../escape.html|",
            )
            with self.assertRaisesRegex(DeployExecutionError, "unsafe bundle member"):
                BundleVerifier().inspect(traversal)

            for link_kind in ("symlink", "hardlink"):
                with self.subTest(link_kind=link_kind):
                    package = root / f"package-{link_kind}"
                    shutil.copytree(layout.site, package / "site")
                    shutil.copy2(layout.manifest, package / "release-manifest.json")
                    link = package / "site" / "linked.html"
                    if link_kind == "symlink":
                        link.symlink_to("index.html")
                    else:
                        link.hardlink_to(package / "site" / "index.html")
                    linked = root / f"{link_kind}.tar.zst"
                    self._write_raw_bundle(package, linked)
                    with self.assertRaisesRegex(
                        DeployExecutionError,
                        "links or special",
                    ):
                        BundleVerifier().inspect(linked)

    def test_bundle_verbose_listing_reports_regular_file_sizes(self) -> None:
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            _spec, full, _release_set, layout = self._self_hosted_package(root)

            members = BundleVerifier()._list_archive(Path(full.bundle))
            by_name = {member.name: member for member in members}

            self.assertEqual(by_name["site/index.html"].kind, "-")
            self.assertEqual(
                by_name["site/index.html"].size,
                (layout.site / "index.html").stat().st_size,
            )
            self.assertEqual(by_name["site/"].kind, "d")

    def test_bundle_metadata_limits_precede_json_reads(self) -> None:
        members = (
            _ArchiveMember("release-manifest.json", "-", 1),
            _ArchiveMember("site/", "d", 0),
            _ArchiveMember("site/release-spec.json", "-", 1),
        )
        with tempfile.TemporaryDirectory() as temp:
            bundle = Path(temp) / "fixture.tar.zst"
            bundle.write_bytes(b"fixture")
            for oversized_name in (
                "release-manifest.json",
                "site/release-spec.json",
            ):
                with self.subTest(member=oversized_name):
                    oversized = tuple(
                        _ArchiveMember(
                            member.name,
                            member.kind,
                            2 if member.name == oversized_name else member.size,
                        )
                        for member in members
                    )
                    verifier = BundleVerifier(max_manifest_bytes=1)
                    with (
                        patch.object(
                            verifier,
                            "_list_archive",
                            return_value=oversized,
                        ),
                        patch.object(
                            verifier,
                            "_read_archive_json",
                            side_effect=AssertionError("JSON read before preflight"),
                        ) as read_json,
                    ):
                        with self.assertRaisesRegex(
                            DeployExecutionError,
                            "exceeds its safety limit",
                        ):
                            verifier.inspect(bundle)
                    read_json.assert_not_called()

    def test_bundle_preflight_rejects_escaped_and_control_names(self) -> None:
        verifier = BundleVerifier()
        metadata = (
            _ArchiveMember("release-manifest.json", "-", 1),
            _ArchiveMember("site/", "d", 0),
            _ArchiveMember("site/release-spec.json", "-", 1),
        )
        for unsafe_name in (
            "site/back\\slash.html",
            "site/new\nline.html",
            "site/nul\0name.html",
            "site/delete\x7fname.html",
        ):
            with self.subTest(name=repr(unsafe_name)):
                with self.assertRaisesRegex(
                    DeployExecutionError,
                    "unsafe bundle member",
                ):
                    verifier._validate_members(
                        (*metadata, _ArchiveMember(unsafe_name, "-", 1))
                    )

    def test_bundle_preflight_rejects_path_aliases_and_duplicates(self) -> None:
        verifier = BundleVerifier()
        metadata = (
            _ArchiveMember("release-manifest.json", "-", 1),
            _ArchiveMember("site/", "d", 0),
            _ArchiveMember("site/release-spec.json", "-", 1),
        )
        for alias in (
            "site//alias.html",
            "site/./alias.html",
            "site/alias.html/",
        ):
            with self.subTest(alias=alias):
                with self.assertRaisesRegex(
                    DeployExecutionError,
                    "unsafe bundle member",
                ):
                    verifier._validate_members(
                        (*metadata, _ArchiveMember(alias, "-", 1))
                    )

        with self.assertRaisesRegex(
            DeployExecutionError,
            "duplicate archive members",
        ):
            verifier._validate_members(
                (*metadata, _ArchiveMember("site/release-spec.json", "-", 1))
            )

    def test_self_hosted_health_url_is_restricted_to_safe_http_urls(self) -> None:
        for health_url in (
            "file:///srv/reasbook/release-spec.json",
            "http:///missing-host",
            "http://user:secret@example.test/health",
            "https://example.test/health#fragment",
            "http://example.test:invalid/health",
        ):
            with self.subTest(health_url=health_url):
                with self.assertRaisesRegex(DeployConfigError, "health URL"):
                    SelfHostedInstaller._validate_options(
                        "full",
                        1,
                        0.01,
                        health_url=health_url,
                        filesystem_health_only=False,
                    )

        SelfHostedInstaller._validate_options(
            "full",
            1,
            0.01,
            health_url="http://127.0.0.1/ReasBook/release-spec.json",
            filesystem_health_only=False,
        )

    def test_bundle_preflight_rejects_header_totals_that_disagree(self) -> None:
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            _spec, _full, _release_set, layout = self._self_hosted_package(root)
            package = root / "mismatched-package"
            shutil.copytree(layout.site, package / "site")
            value = json.loads(layout.manifest.read_text(encoding="utf-8"))
            value["total_bytes"] += 1
            (package / "release-manifest.json").write_text(
                json.dumps(value),
                encoding="utf-8",
            )
            archive = root / "mismatched.tar.zst"
            self._write_raw_bundle(package, archive)

            with self.assertRaisesRegex(
                DeployExecutionError,
                "archive sizes do not match",
            ):
                BundleVerifier().inspect(archive)

    def test_self_hosted_release_set_mismatch_leaves_root_untouched(self) -> None:
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            _spec, full, release_set, _layout = self._self_hosted_package(root)
            value = json.loads(release_set.read_text(encoding="utf-8"))
            full_record = next(
                item for item in value["artifacts"] if item["name"] == "full"
            )
            full_record["total_bytes"] += 1
            forged = root / "forged-release-set.json"
            forged.write_text(json.dumps(value), encoding="utf-8")
            deployment_root = root / "server"

            with self.assertRaisesRegex(DeployExecutionError, "does not bind"):
                SelfHostedInstaller(deployment_root).install(
                    Path(full.bundle),
                    release_set=forged,
                    expected_artifact_policy_sha256=artifact_policy_digest(
                        profile(root).artifacts
                    ),
                    expected_sha256=full.bundle_sha256,
                    filesystem_health_only=True,
                )
            self.assertFalse(deployment_root.exists())

    def test_self_hosted_health_failure_restores_previous_release(self) -> None:
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            first_spec, first_bundle, first_release_set, _ = (
                self._self_hosted_package(root, content="first")
            )
            second_spec, second_bundle, second_release_set, _ = (
                self._self_hosted_package(
                    root,
                    generated_at=self.now.replace(minute=1),
                    content="second",
                )
            )
            installer = SelfHostedInstaller(root / "server")
            installer.install(
                Path(first_bundle.bundle),
                release_set=first_release_set,
                expected_artifact_policy_sha256=artifact_policy_digest(
                    profile(root).artifacts
                ),
                expected_sha256=first_bundle.bundle_sha256,
                filesystem_health_only=True,
            )
            with patch.object(
                installer,
                "_probe",
                side_effect=DeployExecutionError("unhealthy"),
            ):
                with self.assertRaisesRegex(DeployExecutionError, "unhealthy"):
                    installer.install(
                        Path(second_bundle.bundle),
                        release_set=second_release_set,
                        expected_artifact_policy_sha256=artifact_policy_digest(
                            profile(root).artifacts
                        ),
                        expected_sha256=second_bundle.bundle_sha256,
                        health_url="http://127.0.0.1/health",
                    )

            active = (root / "server" / "current").resolve()
            self.assertEqual(
                active,
                root / "server" / "releases" / first_spec.release_id / "full",
            )
            self.assertNotEqual(first_spec.release_id, second_spec.release_id)

    def test_self_hosted_signal_during_install_restores_previous_release(self) -> None:
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            first_spec, first_bundle, first_release_set, _ = (
                self._self_hosted_package(root, content="first")
            )
            _second_spec, second_bundle, second_release_set, _ = (
                self._self_hosted_package(
                    root,
                    generated_at=self.now.replace(minute=1),
                    content="second",
                )
            )
            installer = SelfHostedInstaller(root / "server")
            installer.install(
                Path(first_bundle.bundle),
                release_set=first_release_set,
                expected_artifact_policy_sha256=artifact_policy_digest(
                    profile(root).artifacts
                ),
                expected_sha256=first_bundle.bundle_sha256,
                filesystem_health_only=True,
            )

            with patch.object(installer, "_probe", side_effect=SystemExit(143)):
                with self.assertRaises(SystemExit) as raised:
                    installer.install(
                        Path(second_bundle.bundle),
                        release_set=second_release_set,
                        expected_artifact_policy_sha256=artifact_policy_digest(
                            profile(root).artifacts
                        ),
                        expected_sha256=second_bundle.bundle_sha256,
                        health_url="http://127.0.0.1/health",
                    )

            self.assertEqual(raised.exception.code, 143)
            self.assertEqual(
                (root / "server" / "current").resolve(),
                root / "server" / "releases" / first_spec.release_id / "full",
            )

    def test_self_hosted_rollback_health_failure_restores_active_release(self) -> None:
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            first_spec, first_bundle, first_set, _ = self._self_hosted_package(
                root,
                content="first",
            )
            second_spec, second_bundle, second_set, _ = self._self_hosted_package(
                root,
                generated_at=self.now.replace(minute=1),
                content="second",
            )
            installer = SelfHostedInstaller(root / "server")
            installer.install(
                Path(first_bundle.bundle),
                release_set=first_set,
                expected_artifact_policy_sha256=artifact_policy_digest(
                    profile(root).artifacts
                ),
                expected_sha256=first_bundle.bundle_sha256,
                filesystem_health_only=True,
            )
            installer.install(
                Path(second_bundle.bundle),
                release_set=second_set,
                expected_artifact_policy_sha256=artifact_policy_digest(
                    profile(root).artifacts
                ),
                expected_sha256=second_bundle.bundle_sha256,
                filesystem_health_only=True,
            )

            with patch.object(
                installer,
                "_probe",
                side_effect=DeployExecutionError("unhealthy rollback"),
            ):
                with self.assertRaisesRegex(
                    DeployExecutionError,
                    "unhealthy rollback",
                ):
                    installer.rollback(
                        first_spec.release_id,
                        health_url="http://127.0.0.1/health",
                    )

            self.assertEqual(
                (root / "server" / "current").resolve(),
                root / "server" / "releases" / second_spec.release_id / "full",
            )

    def test_self_hosted_signal_during_rollback_restores_active_release(self) -> None:
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            first_spec, first_bundle, first_set, _ = self._self_hosted_package(
                root,
                content="first",
            )
            second_spec, second_bundle, second_set, _ = self._self_hosted_package(
                root,
                generated_at=self.now.replace(minute=1),
                content="second",
            )
            installer = SelfHostedInstaller(root / "server")
            for bundle, release_set in (
                (first_bundle, first_set),
                (second_bundle, second_set),
            ):
                installer.install(
                    Path(bundle.bundle),
                    release_set=release_set,
                    expected_artifact_policy_sha256=artifact_policy_digest(
                        profile(root).artifacts
                    ),
                    expected_sha256=bundle.bundle_sha256,
                    filesystem_health_only=True,
                )

            with patch.object(installer, "_probe", side_effect=SystemExit(143)):
                with self.assertRaises(SystemExit) as raised:
                    installer.rollback(
                        first_spec.release_id,
                        health_url="http://127.0.0.1/health",
                    )

            self.assertEqual(raised.exception.code, 143)
            self.assertEqual(
                (root / "server" / "current").resolve(),
                root / "server" / "releases" / second_spec.release_id / "full",
            )

    @staticmethod
    def _write_branch_site(
        root: Path,
        *,
        books: dict[str, str],
        papers: dict[str, str],
    ) -> None:
        root.mkdir(parents=True)
        (root / "index.html").write_text("branch", encoding="utf-8")
        for kind, projects, leaf in (
            ("books", books, "Book"),
            ("papers", papers, "Paper"),
        ):
            kind_title = "Books" if kind == "books" else "Papers"
            for project, content in projects.items():
                slug = project.lower()
                pages = root / kind / slug
                (pages / "chapter").mkdir(parents=True)
                html_content = f"<!doctype html><html><body>{content}</body></html>"
                (pages / "index.html").write_text(
                    html_content,
                    encoding="utf-8",
                )
                (pages / "chapter" / "index.html").write_text(
                    "<!doctype html><html><body>chapter</body></html>",
                    encoding="utf-8",
                )
                docs = root / "docs" / "ReasBook" / kind_title / project
                docs.mkdir(parents=True)
                (docs / f"{leaf}.html").write_text(
                    html_content,
                    encoding="utf-8",
                )
                theorem_map = root / "theorem-maps" / kind / slug
                theorem_map.mkdir(parents=True)
                (theorem_map / "index.html").write_text(
                    html_content,
                    encoding="utf-8",
                )

    def test_github_publisher_uploads_then_dispatches_pages(self) -> None:
        class FakeRunner:
            def __init__(self):
                self.commands = []

            def run(self, command):
                self.commands.append(command)
                if command.argv == ("git", "rev-parse", "HEAD"):
                    return CommandResult(
                        command=command, returncode=0, stdout="d" * 40 + "\n"
                    )
                if command.argv[0] == "git":
                    return CommandResult(command=command, returncode=0, stdout="")
                if command.argv[1:3] == ("repo", "view"):
                    return CommandResult(command=command, returncode=0, stdout="main\n")
                if command.argv[1] == "api":
                    if "/releases/tags/" in command.argv[2]:
                        return CommandResult(
                            command=command,
                            returncode=1,
                            stderr="gh: Not Found (HTTP 404)",
                        )
                    if "/commits/" in command.argv[2]:
                        return CommandResult(
                            command=command, returncode=0, stdout="d" * 40 + "\n"
                        )
                    return CommandResult(
                        command=command,
                        returncode=0,
                        stdout=json.dumps(
                            {"object": {"type": "commit", "sha": "c" * 40}}
                        ),
                    )
                return CommandResult(command=command, returncode=0)

        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            release_id = "site-20260901T140000Z-" + "a" * 12
            bundle, assets = github_pages_bundle_fixture(root, release_id)
            runner = FakeRunner()
            publisher = GitHubReleasePublisher(
                GitHubPublishProfile(repository="acme/reasbook"),
                runner=runner,
            )
            publication = publisher.publish(bundle)

            verbs = [command.argv[1:3] for command in runner.commands]
            self.assertEqual(
                verbs,
                [
                    (
                        "api",
                        "repos/acme/reasbook/releases/tags/"
                        "reasbook-site-20260901T140000Z-aaaaaaaaaaaa",
                    ),
                    ("repo", "view"),
                    ("api", "repos/acme/reasbook/commits/main"),
                    ("rev-parse", "HEAD"),
                    ("status", "--porcelain=v1"),
                    ("release", "create"),
                    ("release", "upload"),
                    ("release", "edit"),
                    ("workflow", "run"),
                ],
            )
            self.assertEqual(publication.status, "dispatched")
            self.assertNotIn("secret", " ".join(runner.commands[-1].argv))
            self.assertNotIn(
                "--clobber",
                " ".join(part for command in runner.commands for part in command.argv),
            )
            workflow_command = runner.commands[-1].argv
            self.assertEqual(workflow_command.count("-f"), 1)
            self.assertIn("--ref", workflow_command)
            self.assertEqual(
                workflow_command[workflow_command.index("--ref") + 1],
                "main",
            )

    def test_github_release_lookup_fails_closed_on_non_404_error(self) -> None:
        class FailedLookupRunner:
            def run(self, command):
                return CommandResult(
                    command=command,
                    returncode=1,
                    stderr="gh: HTTP 403: rate limit exceeded",
                )

        publisher = GitHubReleasePublisher(
            GitHubPublishProfile(repository="acme/reasbook"),
            runner=FailedLookupRunner(),
        )
        with self.assertRaisesRegex(
            DeployExecutionError, "release lookup failed.*403"
        ):
            publisher._release_by_tag("reasbook-site-safe")

    def test_github_new_release_requires_synced_clean_default_branch(self) -> None:
        class CheckoutRunner:
            def __init__(self, *, head: str, status: str = ""):
                self.head = head
                self.status = status

            def run(self, command):
                if command.argv[0] == "git":
                    output = self.head if command.argv[1] == "rev-parse" else self.status
                    return CommandResult(command=command, returncode=0, stdout=output)
                if command.argv[1:3] == ("repo", "view"):
                    return CommandResult(command=command, returncode=0, stdout="main\n")
                return CommandResult(
                    command=command,
                    returncode=0,
                    stdout="d" * 40 + "\n",
                )

        profile = GitHubPublishProfile(repository="acme/reasbook")
        with self.assertRaisesRegex(DeployExecutionError, "local HEAD"):
            GitHubReleasePublisher(
                profile,
                runner=CheckoutRunner(head="c" * 40 + "\n"),
            )._trusted_target()
        with self.assertRaisesRegex(DeployExecutionError, "clean Git"):
            GitHubReleasePublisher(
                profile,
                runner=CheckoutRunner(
                    head="d" * 40 + "\n",
                    status="?? uncommitted.py\n",
                ),
            )._trusted_target()

    def test_github_pages_configuration_is_idempotent_and_fail_closed(self) -> None:
        class ConfigureRunner:
            def __init__(self):
                self.commands = []
                self.pages = None
                self.environment = None
                self.policies = None

            def run(self, command):
                self.commands.append(command)
                if command.argv[0] == "git":
                    output = (
                        "d" * 40 + "\n"
                        if command.argv[1:3] == ("rev-parse", "HEAD")
                        else ""
                    )
                    return CommandResult(command=command, returncode=0, stdout=output)
                if command.argv[1:3] == ("repo", "view"):
                    return CommandResult(command=command, returncode=0, stdout="main\n")
                if command.argv[1] != "api":
                    return CommandResult(command=command, returncode=0)
                if "/commits/" in " ".join(command.argv):
                    return CommandResult(
                        command=command,
                        returncode=0,
                        stdout="d" * 40 + "\n",
                    )
                endpoint = next(
                    part for part in command.argv if part.startswith("repos/")
                )
                method = (
                    command.argv[command.argv.index("--method") + 1]
                    if "--method" in command.argv
                    else "GET"
                )
                if method == "POST" and endpoint.endswith("/pages"):
                    self.pages = {"build_type": "workflow", "cname": None}
                    value = self.pages
                elif method == "PUT" and endpoint.endswith("/github-pages"):
                    self.environment = {
                        "deployment_branch_policy": {
                            "protected_branches": False,
                            "custom_branch_policies": True,
                        }
                    }
                    value = self.environment
                elif method == "POST" and endpoint.endswith(
                    "/deployment-branch-policies"
                ):
                    request = json.loads(command.input_text or "{}")
                    self.policies = {
                        "total_count": 1,
                        "branch_policies": [request],
                    }
                    value = request
                elif endpoint.endswith("/pages"):
                    value = self.pages
                elif endpoint.split("?", 1)[0].endswith(
                    "/deployment-branch-policies"
                ):
                    value = self.policies
                else:
                    value = self.environment
                if value is None:
                    return CommandResult(
                        command=command,
                        returncode=1,
                        stderr="gh: Not Found (HTTP 404)",
                    )
                return CommandResult(
                    command=command,
                    returncode=0,
                    stdout=json.dumps(value),
                )

        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            workflow = root / ".github" / "workflows" / "publish_release_pages.yml"
            workflow.parent.mkdir(parents=True)
            workflow.write_text("name: pages\n", encoding="utf-8")
            runner = ConfigureRunner()
            configurator = GitHubPagesConfigurator(
                GitHubPublishProfile(repository="acme/reasbook"),
                runner=runner,
                repo_root=root,
            )

            planned = configurator.configure(dry_run=True)
            self.assertEqual(planned.status, "planned")
            self.assertEqual(
                planned.actions,
                (
                    "create-pages-workflow-source",
                    "create-github-pages-environment",
                    "allow-default-branch-only",
                ),
            )
            self.assertFalse(
                any("--method" in command.argv for command in runner.commands)
            )

            configured = configurator.configure()
            self.assertEqual(configured.status, "configured")
            writes = [
                command for command in runner.commands if "--method" in command.argv
            ]
            self.assertEqual(
                [command.argv[command.argv.index("--method") + 1] for command in writes],
                ["POST", "PUT", "POST"],
            )
            self.assertEqual(
                json.loads(writes[-1].input_text or "{}"),
                {"name": "main", "type": "branch"},
            )

            before = len(writes)
            ready = configurator.configure()
            self.assertEqual(ready.status, "ready")
            after = sum("--method" in command.argv for command in runner.commands)
            self.assertEqual(after, before)

            runner.policies = {
                "total_count": 2,
                "branch_policies": [
                    {"name": "main", "type": "branch"},
                    {"name": "v4.30.0", "type": "branch"},
                ],
            }
            before = sum("--method" in command.argv for command in runner.commands)
            with self.assertRaisesRegex(DeployExecutionError, "default branch"):
                configurator.configure()
            after = sum("--method" in command.argv for command in runner.commands)
            self.assertEqual(after, before)

    def test_github_publisher_rejects_full_artifact(self) -> None:
        class NoRunner:
            def run(self, _command):
                raise AssertionError("GitHub must not be called for a full artifact")

        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            release_id = "site-20260901T140000Z-" + "a" * 12
            bundle = root / f"{release_id}.site.tar.zst"
            bundle.write_text("fixture", encoding="utf-8")
            digest = hashlib.sha256(bundle.read_bytes()).hexdigest()
            manifest = root / "release-manifest.json"
            manifest.write_text(
                json.dumps(release_manifest_fixture(release_id)),
                encoding="utf-8",
            )
            checksums = root / "SHA256SUMS"
            checksums.write_text(f"{digest}  {bundle.name}\n", encoding="utf-8")
            with self.assertRaisesRegex(DeployExecutionError, "pages artifact"):
                GitHubReleasePublisher(
                    GitHubPublishProfile(repository="acme/reasbook"),
                    runner=NoRunner(),
                ).publish(
                    BundleInfo(
                        release_id,
                        str(bundle),
                        str(manifest),
                        str(checksums),
                        "sha256:" + digest,
                    )
                )

    def test_github_pages_assets_are_bound_by_release_set(self) -> None:
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            release_id = "site-20260901T140000Z-" + "a" * 12
            bundle_path = root / f"{release_id}.pages.site.tar.zst"
            bundle_path.write_text("fixture", encoding="utf-8")
            digest = hashlib.sha256(bundle_path.read_bytes()).hexdigest()
            site_digest = "sha256:" + "b" * 64
            spec_digest = "sha256:" + "a" * 64
            manifest_path = root / "release-manifest.json"
            manifest_path.write_text(
                json.dumps(
                    release_manifest_fixture(
                        release_id,
                        artifact="pages",
                        spec_digest=spec_digest,
                        site_digest=site_digest,
                    )
                ),
                encoding="utf-8",
            )
            checksums_path = root / "SHA256SUMS"
            checksums_path.write_text(
                f"{digest}  {bundle_path.name}\n", encoding="utf-8"
            )
            release_set_path = root / "release-set.json"
            release_set_path.write_text(
                json.dumps(
                    {
                        "schema_version": 1,
                        "release_id": release_id,
                        "spec_digest": spec_digest,
                        "generated_at": "2026-09-01T14:00:00Z",
                        "artifact_policy_sha256": "sha256:" + "c" * 64,
                        "artifacts": [
                            {
                                "name": "full",
                                "bundle": f"{release_id}.site.tar.zst",
                                "bundle_sha256": "sha256:" + "d" * 64,
                                "site_tree_sha256": "sha256:" + "e" * 64,
                                "file_count": 2,
                                "total_bytes": 8,
                            },
                            {
                                "name": "pages",
                                "bundle": bundle_path.name,
                                "bundle_sha256": "sha256:" + digest,
                                "site_tree_sha256": site_digest,
                                "file_count": 1,
                                "total_bytes": 7,
                            }
                        ],
                    }
                ),
                encoding="utf-8",
            )
            bundle = BundleInfo(
                release_id,
                str(bundle_path),
                str(manifest_path),
                str(checksums_path),
                "sha256:" + digest,
                artifact="pages",
                release_set=str(release_set_path),
            )
            GitHubReleasePublisher._validate_assets(
                bundle,
                (bundle_path, manifest_path, checksums_path, release_set_path),
                expected_base_path="/ReasBook/",
                expected_spec_digest=spec_digest,
                expected_artifact_policy_sha256="sha256:" + "c" * 64,
            )

            with self.assertRaisesRegex(DeployExecutionError, "expected Pages"):
                GitHubReleasePublisher._validate_assets(
                    bundle,
                    (bundle_path, manifest_path, checksums_path, release_set_path),
                    expected_base_path="/wrong/",
                )
            with self.assertRaisesRegex(DeployExecutionError, "does not bind"):
                GitHubReleasePublisher._validate_assets(
                    bundle,
                    (bundle_path, manifest_path, checksums_path, release_set_path),
                    expected_artifact_policy_sha256="sha256:" + "0" * 64,
                )

            release_set_path.write_text(
                release_set_path.read_text(encoding="utf-8").replace(
                    "sha256:" + digest, "sha256:" + "0" * 64
                ),
                encoding="utf-8",
            )
            with self.assertRaisesRegex(DeployExecutionError, "does not bind"):
                GitHubReleasePublisher._validate_assets(
                    bundle,
                    (bundle_path, manifest_path, checksums_path, release_set_path),
                )

    def test_github_wait_ignores_runs_that_predate_dispatch(self) -> None:
        class WaitRunner:
            def __init__(self, paths):
                self.list_calls = 0
                self.paths = paths
                self.commands = []

            def run(self, command):
                self.commands.append(command)
                if command.argv[1:3] == ("repo", "view"):
                    return CommandResult(command=command, returncode=0, stdout="main\n")
                if command.argv[1] == "api":
                    if "/releases/tags/" in command.argv[2]:
                        assets = [
                            {
                                "name": path.name,
                                "size": path.stat().st_size,
                                "digest": "sha256:"
                                + hashlib.sha256(path.read_bytes()).hexdigest(),
                            }
                            for path in self.paths
                        ]
                        return CommandResult(
                            command=command,
                            returncode=0,
                            stdout=json.dumps(
                                {
                                    "draft": False,
                                    "target_commitish": "c" * 40,
                                    "assets": assets,
                                }
                            ),
                        )
                    if "/commits/" in command.argv[2]:
                        return CommandResult(
                            command=command, returncode=0, stdout="d" * 40 + "\n"
                        )
                    return CommandResult(
                        command=command,
                        returncode=0,
                        stdout=json.dumps(
                            {"object": {"type": "commit", "sha": "c" * 40}}
                        ),
                    )
                if command.argv[1:3] == ("run", "list"):
                    self.list_calls += 1
                    if self.list_calls == 1:
                        payload = [{"databaseId": 10}]
                    else:
                        payload = [
                            {
                                "databaseId": 10,
                                "displayTitle": (
                                    "Publish reasbook-site-"
                                    "20260901T140000Z-aaaaaaaaaaaa"
                                ),
                                "status": "completed",
                                "conclusion": "success",
                            },
                            {
                                "databaseId": 11,
                                "displayTitle": (
                                    "Publish reasbook-site-"
                                    "20260901T140000Z-aaaaaaaaaaaa"
                                ),
                                "status": "completed",
                                "conclusion": "success",
                            },
                        ]
                    return CommandResult(
                        command=command,
                        returncode=0,
                        stdout=json.dumps(payload),
                    )
                return CommandResult(command=command, returncode=0)

        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            release_id = "site-20260901T140000Z-" + "a" * 12
            bundle, paths = github_pages_bundle_fixture(root, release_id)
            runner = WaitRunner(paths)
            publication = GitHubReleasePublisher(
                GitHubPublishProfile(repository="acme/reasbook"),
                runner=runner,
            ).publish(
                bundle,
                wait=True,
                wait_timeout_seconds=1,
            )
            self.assertEqual(publication.run_id, 11)
            self.assertEqual(
                publication.tag,
                "reasbook-site-20260901T140000Z-aaaaaaaaaaaa",
            )
            workflow = next(
                command for command in runner.commands
                if command.argv[1:3] == ("workflow", "run")
            )
            self.assertEqual(
                workflow.argv[workflow.argv.index("--ref") + 1], "main"
            )
            verbs = [command.argv[1:3] for command in runner.commands]
            self.assertIn(("repo", "view"), verbs)
            self.assertFalse(
                any(
                    command.argv[1] == "api" and "/commits/" in command.argv[2]
                    for command in runner.commands
                ),
                "rollback of an old tag must not depend on the current default branch",
            )

    def test_github_publisher_refuses_to_replace_existing_assets(self) -> None:
        class ExistingRunner:
            def __init__(self):
                self.commands = []

            def run(self, command):
                self.commands.append(command)
                if command.argv[1:3] == ("repo", "view"):
                    return CommandResult(command=command, returncode=0, stdout="main\n")
                if command.argv[1] == "api":
                    if "/releases/tags/" in command.argv[2]:
                        return CommandResult(
                            command=command,
                            returncode=0,
                            stdout=json.dumps(
                                {
                                    "draft": False,
                                    "target_commitish": "c" * 40,
                                    "assets": [
                                        {
                                            "name": "unexpected.site.tar.zst",
                                            "size": 1,
                                            "digest": "sha256:" + "0" * 64,
                                        }
                                    ],
                                }
                            ),
                        )
                    if "/commits/" in command.argv[2]:
                        return CommandResult(
                            command=command, returncode=0, stdout="d" * 40 + "\n"
                        )
                    return CommandResult(
                        command=command,
                        returncode=0,
                        stdout=json.dumps(
                            {"object": {"type": "commit", "sha": "c" * 40}}
                        ),
                    )
                return CommandResult(command=command, returncode=0)

        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            release_id = "site-20260901T140000Z-" + "a" * 12
            bundle, _ = github_pages_bundle_fixture(root, release_id)
            runner = ExistingRunner()

            with self.assertRaisesRegex(DeployExecutionError, "refusing to overwrite"):
                GitHubReleasePublisher(
                    GitHubPublishProfile(repository="acme/reasbook"), runner=runner
                ).publish(bundle)

            verbs = [command.argv[1:3] for command in runner.commands]
            self.assertNotIn(("release", "upload"), verbs)
            self.assertNotIn(("workflow", "run"), verbs)

    def test_resume_reuses_successful_branch_build_before_assembly(self) -> None:
        class FakeBuilder:
            def __init__(self, report):
                self.report = report
                self.calls = 0

            def build(self, _spec):
                self.calls += 1
                return self.report

        class FailedAssembler:
            def assemble(self, _spec, _report):
                raise RuntimeError("assembly failed")

        class SuccessfulAssembler:
            def __init__(self, site):
                self.site = site

            def assemble(self, _spec, _report):
                self.site.mkdir(parents=True, exist_ok=True)
                return self.site

        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            spec = self._spec(root)
            layout = ReleaseLayout(root / "cache", spec.release_id)
            store = ReleaseStore(layout)
            state = store.initialize(spec)
            report = ReleaseBuildReport.from_branches(
                spec,
                tuple(
                    BranchBuildResult(
                        branch.name,
                        branch.commit,
                        "success",
                        str(root / branch.name),
                        (StageOutcome("fixture", "success"),),
                    )
                    for branch in spec.branches
                ),
            )
            builder = FakeBuilder(report)
            context = ReleaseContext(profile(root), spec, layout, state)
            service = StaticReleaseService(
                root,
                root / "cache",
                tooling_root=REPO_ROOT,
                source=FakeReleaseSource(),
            )
            with self.assertRaisesRegex(RuntimeError, "assembly failed"):
                service.build(
                    context,
                    builder=builder,
                    assembler=FailedAssembler(),
                )
            self.assertIn("build", store.load_state().completed)

            service.build(
                context,
                builder=builder,
                assembler=SuccessfulAssembler(layout.site),
            )
            self.assertEqual(builder.calls, 1)
            self.assertIn("site", store.load_state().completed)


if __name__ == "__main__":
    unittest.main()
