from __future__ import annotations

from datetime import datetime, timezone
import json
import hashlib
from pathlib import Path
import shutil
import tempfile
import unittest
from unittest.mock import patch

from reasbook_sdk_common import CommandResult
from reasbook_deploy_sdk import DeployConfigError, DeployExecutionError
from reasbook_deploy_sdk.release.build_plan import (
    BranchPlanFactory,
    ReleaseBuildOptions,
)
from reasbook_deploy_sdk.release.bundle import BundleVerifier, ReleaseBundler
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
    RegistryBranch,
    ReleasePolicy,
    ReleaseSpec,
    SourceProject,
    ToolchainRegistry,
)
from reasbook_deploy_sdk.release.planner import ReleasePlanner
from reasbook_deploy_sdk.release.github import GitHubReleasePublisher
from reasbook_deploy_sdk.release.results import (
    BranchBuildResult,
    BundleInfo,
    ReleaseBuildReport,
    StageOutcome,
)
from reasbook_deploy_sdk.release.site import ReleaseSiteAssembler
from reasbook_deploy_sdk.release.service import (
    ReleaseContext,
    StaticReleaseService,
)
from reasbook_deploy_sdk.release.source import _credential_free_remote
from reasbook_deploy_sdk.release.store import ReleaseLayout, ReleaseStore
from reasbook_deploy_sdk.release.tooling import (
    bind_tooling_revision,
    tooling_digest_from_revision,
)


REPO_ROOT = Path(__file__).resolve().parents[3]


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
                    "docs-demo",
                    "docs-onlyold",
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
            bundle_path = root / f"{release_id}.site.tar.zst"
            bundle_path.write_text("fixture", encoding="utf-8")
            digest = hashlib.sha256(bundle_path.read_bytes()).hexdigest()
            manifest_path = root / "release-manifest.json"
            manifest_path.write_text(
                json.dumps({"release_id": release_id}), encoding="utf-8"
            )
            checksums_path = root / "SHA256SUMS"
            checksums_path.write_text(
                f"{digest}  {bundle_path.name}\n", encoding="utf-8"
            )
            assets = [bundle_path, manifest_path, checksums_path]
            bundle = BundleInfo(
                release_id,
                str(assets[0]),
                str(assets[1]),
                str(assets[2]),
                "sha256:" + digest,
            )
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
                publication.tag,
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
            bundle_path = root / f"{release_id}.site.tar.zst"
            bundle_path.write_text("fixture", encoding="utf-8")
            digest = hashlib.sha256(bundle_path.read_bytes()).hexdigest()
            manifest_path = root / "release-manifest.json"
            manifest_path.write_text(
                json.dumps({"release_id": release_id}), encoding="utf-8"
            )
            checksums_path = root / "SHA256SUMS"
            checksums_path.write_text(
                f"{digest}  {bundle_path.name}\n", encoding="utf-8"
            )
            paths = [bundle_path, manifest_path, checksums_path]
            runner = WaitRunner(paths)
            publication = GitHubReleasePublisher(
                GitHubPublishProfile(repository="acme/reasbook"),
                runner=runner,
            ).publish(
                BundleInfo(
                    release_id,
                    str(paths[0]),
                    str(paths[1]),
                    str(paths[2]),
                    "sha256:" + digest,
                ),
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
                workflow.argv[workflow.argv.index("--ref") + 1], publication.tag
            )
            verbs = [command.argv[1:3] for command in runner.commands]
            self.assertNotIn(("repo", "view"), verbs)
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
            archive = root / f"{release_id}.site.tar.zst"
            archive.write_text("fixture", encoding="utf-8")
            digest = hashlib.sha256(archive.read_bytes()).hexdigest()
            manifest = root / "release-manifest.json"
            manifest.write_text(
                json.dumps({"release_id": release_id}), encoding="utf-8"
            )
            checksums = root / "SHA256SUMS"
            checksums.write_text(
                f"{digest}  {archive.name}\n", encoding="utf-8"
            )
            runner = ExistingRunner()

            with self.assertRaisesRegex(DeployExecutionError, "refusing to overwrite"):
                GitHubReleasePublisher(
                    GitHubPublishProfile(repository="acme/reasbook"), runner=runner
                ).publish(
                    BundleInfo(
                        release_id,
                        str(archive),
                        str(manifest),
                        str(checksums),
                        "sha256:" + digest,
                    )
                )

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
