"""Release use cases composed from planning, build, bundle, and publish adapters."""

from __future__ import annotations

from dataclasses import dataclass
from pathlib import Path
from typing import Any, Iterable, Mapping

from reasbook_sdk_common import atomic_write_text

from ..errors import DeployError, DeployExecutionError
from .acceptance import ReleaseAcceptanceRunner
from .builder import LocalReleaseBuilder
from .build_plan import ReleaseBuildOptions
from .artifacts import PagesSiteProjector, artifact_policy_digest, create_release_set
from .bundle import BundleVerifier, ReleaseBundler
from .config import (
    dump_profile_snapshot,
    load_canonical_projects,
    load_profile,
    load_registry,
)
from .github import GitHubPublication, GitHubReleasePublisher
from .models import DeploymentProfile, ReleaseArtifactPolicy, ReleaseSpec
from .planner import ReleasePlanner
from .promotion import require_release_acceptance
from .results import BundleInfo, ReleaseBuildReport, ReleasePackageResult
from .site import ReleaseSiteAssembler
from .source import GitReleaseSource
from .store import ReleaseLayout, ReleaseState, ReleaseStore
from .tooling import tooling_digest_from_revision, tooling_source_digest


def _utc_now() -> str:
    from datetime import datetime, timezone

    return (
        datetime.now(timezone.utc).isoformat(timespec="seconds").replace("+00:00", "Z")
    )


@dataclass(frozen=True)
class ReleaseContext:
    profile: DeploymentProfile
    spec: ReleaseSpec
    layout: ReleaseLayout
    state: ReleaseState


@dataclass(frozen=True)
class ReleaseDeploymentResult:
    context: ReleaseContext
    build: ReleaseBuildReport | None = None
    package: ReleasePackageResult | None = None
    publication: GitHubPublication | None = None

    def public_dict(self):
        return {
            "release": self.context.spec.public_dict(),
            "state": self.context.state.public_dict(),
            "build": self.build.public_dict() if self.build else None,
            "package": self.package.public_dict() if self.package else None,
            "publication": (
                self.publication.public_dict() if self.publication else None
            ),
        }


class StaticReleaseService:
    """Driving API for plan/build/package/publish and one-click deployment."""

    def __init__(
        self,
        repo_root: Path,
        cache_root: Path,
        *,
        tooling_root: Path | None = None,
        source=None,
    ) -> None:
        self.repo_root = Path(repo_root).expanduser().resolve()
        self.cache_root = Path(cache_root).expanduser().resolve(strict=False)
        self.tooling_root = (
            Path(tooling_root).expanduser().resolve()
            if tooling_root
            else self.repo_root
        )
        self.source = source or GitReleaseSource(self.repo_root)

    def plan(
        self,
        profile_path: Path,
        *,
        only: Iterable[str] = (),
        reuse: bool = True,
        persist: bool = True,
        fetch: bool = False,
    ) -> ReleaseContext:
        if fetch:
            self.source.fetch()
        profile = load_profile(profile_path, repo_root=self.repo_root)
        spec = ReleasePlanner(self.source).resolve(
            profile,
            load_registry(profile.registry),
            load_canonical_projects(profile.canonical_projects),
            only=only,
        )
        reused_existing = False
        if reuse:
            existing = ReleaseStore.find_by_digest(self.cache_root, spec.spec_digest)
            if existing is not None:
                existing_layout = ReleaseLayout(self.cache_root, existing.release_id)
                try:
                    existing_profile = load_profile(
                        existing_layout.profile,
                        repo_root=existing_layout.root,
                    )
                except DeployError:
                    existing_profile = None
                if existing_profile is not None and artifact_policy_digest(
                    existing_profile.artifacts
                ) == artifact_policy_digest(profile.artifacts):
                    spec = existing
                    reused_existing = True
        layout = ReleaseLayout(self.cache_root, spec.release_id)
        store = ReleaseStore(layout)
        if layout.root.exists() and not reused_existing:
            raise DeployExecutionError(
                "a release with this timestamp and digest already exists; "
                "retry after one second"
            )
        if not persist:
            return ReleaseContext(
                profile,
                spec,
                layout,
                ReleaseState(
                    spec.release_id,
                    spec.spec_digest,
                    "planned",
                    (),
                    _utc_now(),
                ),
            )
        with store.locked():
            state = store.initialize(spec)
            if not layout.profile.is_file():
                atomic_write_text(
                    layout.profile,
                    dump_profile_snapshot(profile),
                )
            for source, destination in (
                (profile.registry, layout.registry_snapshot),
                (profile.canonical_projects, layout.canonical_snapshot),
            ):
                if not destination.is_file():
                    atomic_write_text(
                        destination,
                        source.read_text(encoding="utf-8"),
                    )
        return ReleaseContext(profile, spec, layout, state)

    def context(self, release_id: str) -> ReleaseContext:
        layout = ReleaseLayout(self.cache_root, release_id)
        store = ReleaseStore(layout)
        spec = store.load_spec()
        profile = load_profile(layout.profile, repo_root=layout.root)
        return ReleaseContext(profile, spec, layout, store.load_state())

    def build(
        self,
        context: ReleaseContext,
        *,
        options: ReleaseBuildOptions | None = None,
        builder: LocalReleaseBuilder | None = None,
        assembler: ReleaseSiteAssembler | None = None,
    ) -> ReleaseBuildReport:
        store = ReleaseStore(context.layout)
        with store.locked():
            state = store.load_state()
            if "site" in state.completed and context.layout.build_report.is_file():
                return store.load_build_report()
            store.transition("building")
            try:
                if "build" in state.completed and context.layout.build_report.is_file():
                    report = store.load_build_report()
                else:
                    release_builder = builder or LocalReleaseBuilder(
                        self.repo_root,
                        self.tooling_root,
                        self.cache_root,
                        context.layout,
                        options=options,
                    )
                    report = release_builder.build(context.spec)
                    store.write_build_report(report)
                    if report.status == "failed":
                        store.transition(
                            "failed",
                            error="one or more branch builds failed",
                        )
                        raise DeployExecutionError(
                            "release build failed; inspect build-report.json"
                        )
                    store.transition("built", completed_stage="build")
                site_assembler = assembler or ReleaseSiteAssembler(
                    self.tooling_root, context.layout
                )
                site_assembler.assemble(context.spec, report)
                store.transition("validated", completed_stage="site")
                return report
            except Exception as exc:
                if store.load_state().status != "failed":
                    store.transition("failed", error=str(exc))
                raise

    def package(
        self,
        context: ReleaseContext,
        *,
        bundler: ReleaseBundler | None = None,
    ) -> ReleasePackageResult:
        store = ReleaseStore(context.layout)
        with store.locked():
            state = store.load_state()
            if "site" not in state.completed:
                raise DeployExecutionError("release site has not been validated")
            expected_tooling = tooling_digest_from_revision(
                context.spec.tooling_revision
            )
            actual_tooling = tooling_source_digest(self.tooling_root)
            if actual_tooling != expected_tooling:
                raise DeployExecutionError(
                    "release packaging tooling differs from the immutable "
                    "ReleaseSpec; create a new release"
                )
            report = store.load_build_report()
            release_bundler = bundler or ReleaseBundler(context.layout, store)
            try:
                verified_artifacts: set[str] = set()
                full_policy = context.profile.artifact("full")
                pages_policy = context.profile.artifact("pages")
                full = self._verified_cached_bundle(
                    store,
                    policy=full_policy,
                )
                if full is None:
                    full = release_bundler.package(
                        context.spec,
                        report,
                        policy=full_policy,
                    )
                else:
                    verified_artifacts.add("full")
                pages = self._verified_cached_bundle(
                    store,
                    policy=pages_policy,
                )
                if pages is None:
                    PagesSiteProjector(
                        max_site_bytes=pages_policy.max_site_bytes
                    ).project(
                        context.spec,
                        context.layout.site,
                        context.layout.pages_site,
                    )
                    pages = release_bundler.package_pages(
                        context.spec,
                        report,
                        policy=pages_policy,
                    )
                else:
                    verified_artifacts.add("pages")
                release_set, bundles = create_release_set(
                    context.layout,
                    store,
                    context.spec,
                    context.profile.artifacts,
                    (full, pages),
                )
                for bundle in bundles:
                    if bundle.artifact in verified_artifacts:
                        continue
                    verifier = BundleVerifier.for_policy(
                        context.profile.artifact(bundle.artifact)
                    )
                    manifest = verifier.verify(
                        Path(bundle.bundle),
                        expected_sha256=bundle.bundle_sha256,
                    )
                    if manifest.artifact != bundle.artifact:
                        raise DeployExecutionError(
                            "verified bundle artifact does not match bundle metadata"
                        )
                store.transition("packaged", completed_stage="package")
                by_name = {bundle.artifact: bundle for bundle in bundles}
                return ReleasePackageResult(
                    full=by_name["full"],
                    pages=by_name["pages"],
                    release_set=release_set,
                )
            except Exception as exc:
                store.transition("failed", error=str(exc))
                raise

    @staticmethod
    def _verified_cached_bundle(
        store: ReleaseStore,
        *,
        policy: ReleaseArtifactPolicy,
    ) -> BundleInfo | None:
        try:
            artifact = policy.name
            bundle = (
                store.load_bundle_info()
                if artifact == "full"
                else store.load_pages_bundle_info()
            )
            if bundle.artifact != artifact:
                return None
            manifest = BundleVerifier.for_policy(policy).verify(
                Path(bundle.bundle),
                expected_sha256=bundle.bundle_sha256,
            )
            return bundle if manifest.artifact == artifact else None
        except (DeployError, OSError):
            return None

    def publish(
        self,
        context: ReleaseContext,
        *,
        wait: bool = False,
        wait_timeout_seconds: float = 1800.0,
        pages_health_timeout_seconds: float = 300.0,
        dry_run: bool = False,
        force: bool = False,
        publisher: GitHubReleasePublisher | None = None,
    ) -> GitHubPublication:
        store = ReleaseStore(context.layout)
        with store.locked():
            state = store.load_state()
            if "package" not in state.completed:
                raise DeployExecutionError("release bundle has not been packaged")
            acceptance = self.require_acceptance(context)
            if (
                "publish" in state.completed
                and context.layout.publication.is_file()
                and not force
                and not dry_run
            ):
                existing = store.load_publication()
                if not wait or existing.status == "published":
                    return existing
            bundle = store.load_pages_bundle_info()
            release_publisher = publisher or GitHubReleasePublisher(
                context.profile.publish,
                repo_root=self.repo_root,
                expected_base_path=context.spec.base_path,
                expected_spec_digest=context.spec.spec_digest,
                expected_artifact_policy_sha256=artifact_policy_digest(
                    context.profile.artifacts
                ),
                expected_registry_commit=context.spec.registry_commit,
                expected_tooling_revision=context.spec.tooling_revision,
                expected_release_set_sha256=str(
                    acceptance["metadata"]["release_set_sha256"]
                ),
                bundle_verifier=BundleVerifier.for_policy(
                    context.profile.artifact("pages")
                ),
            )
            if dry_run:
                return release_publisher.publish(
                    bundle,
                    wait=wait,
                    wait_timeout_seconds=wait_timeout_seconds,
                    pages_health_timeout_seconds=pages_health_timeout_seconds,
                    dry_run=True,
                )
            store.transition("uploading")
            try:
                publication = release_publisher.publish(
                    bundle,
                    wait=wait,
                    wait_timeout_seconds=wait_timeout_seconds,
                    pages_health_timeout_seconds=pages_health_timeout_seconds,
                    dry_run=False,
                )
            except Exception as exc:
                store.transition("failed", error=str(exc))
                raise
            store.write_publication(publication)
            store.transition(
                ("published" if publication.status == "published" else "dispatched"),
                completed_stage="publish",
            )
            return publication

    def validate(
        self,
        context: ReleaseContext,
        *,
        browser_mode: str = "required",
        keep_workdir: bool = False,
    ) -> dict[str, Any]:
        """Run the single local acceptance implementation used for promotion."""

        return ReleaseAcceptanceRunner(
            self.repo_root,
            context.layout,
            context.spec,
            expected_artifact_policy_sha256=artifact_policy_digest(
                context.profile.artifacts
            ),
            artifact_policies=context.profile.artifacts,
        ).run(
            browser_mode=browser_mode,
            keep_workdir=keep_workdir,
        )

    @staticmethod
    def require_acceptance(context: ReleaseContext) -> Mapping[str, Any]:
        """Require current, browser-complete evidence before target mutation."""

        return require_release_acceptance(
            context.layout,
            context.spec,
            expected_artifact_policy_sha256=artifact_policy_digest(
                context.profile.artifacts
            ),
        )

    def promote(
        self,
        context: ReleaseContext,
        *,
        wait: bool = False,
        wait_timeout_seconds: float = 1800.0,
        pages_health_timeout_seconds: float = 300.0,
    ) -> GitHubPublication:
        """Run required acceptance and publish exactly its bound package."""

        self.validate(context, browser_mode="required")
        return self.publish(
            context,
            wait=wait,
            wait_timeout_seconds=wait_timeout_seconds,
            pages_health_timeout_seconds=pages_health_timeout_seconds,
        )

    def deploy(
        self,
        profile_path: Path,
        *,
        only: Iterable[str] = (),
        options: ReleaseBuildOptions | None = None,
        publish: bool = True,
        wait: bool = False,
        wait_timeout_seconds: float = 1800.0,
        pages_health_timeout_seconds: float = 300.0,
        dry_run: bool = False,
        reuse: bool = True,
        fetch: bool = True,
        allow_local_all_active: bool = False,
    ) -> ReleaseDeploymentResult:
        selected = tuple(only)
        if not selected and not dry_run and not allow_local_all_active:
            raise DeployExecutionError(
                "release deploy uses the local builder; select a canary with "
                "--only or explicitly pass --allow-local-all-active-build"
            )
        context = self.plan(
            profile_path,
            only=selected,
            reuse=reuse,
            persist=not dry_run,
            fetch=fetch and not dry_run,
        )
        if dry_run:
            return ReleaseDeploymentResult(context)
        report = self.build(context, options=options)
        package = self.package(context)
        publication = (
            self.promote(
                context,
                wait=wait,
                wait_timeout_seconds=wait_timeout_seconds,
                pages_health_timeout_seconds=pages_health_timeout_seconds,
            )
            if publish
            else None
        )
        refreshed = self.context(context.spec.release_id)
        return ReleaseDeploymentResult(refreshed, report, package, publication)


__all__ = [
    "ReleaseContext",
    "ReleaseDeploymentResult",
    "StaticReleaseService",
]
