"""Release use cases composed from planning, build, bundle, and publish adapters."""

from __future__ import annotations

from dataclasses import dataclass
from pathlib import Path
from typing import Iterable

from reasbook_sdk_common import atomic_write_text

from ..errors import DeployExecutionError
from .builder import LocalReleaseBuilder
from .build_plan import ReleaseBuildOptions
from .bundle import BundleVerifier, ReleaseBundler
from .config import (
    dump_profile_snapshot,
    load_canonical_projects,
    load_profile,
    load_registry,
)
from .github import GitHubPublication, GitHubReleasePublisher
from .models import DeploymentProfile, ReleaseSpec
from .planner import ReleasePlanner
from .results import BundleInfo, ReleaseBuildReport
from .site import ReleaseSiteAssembler
from .source import GitReleaseSource
from .store import ReleaseLayout, ReleaseState, ReleaseStore


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
    bundle: BundleInfo | None = None
    publication: GitHubPublication | None = None

    def public_dict(self):
        return {
            "release": self.context.spec.public_dict(),
            "state": self.context.state.public_dict(),
            "build": self.build.public_dict() if self.build else None,
            "bundle": self.bundle.public_dict() if self.bundle else None,
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
        if reuse:
            existing = ReleaseStore.find_by_digest(self.cache_root, spec.spec_digest)
            if existing is not None:
                spec = existing
        layout = ReleaseLayout(self.cache_root, spec.release_id)
        store = ReleaseStore(layout)
        if not reuse and layout.root.exists():
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
    ) -> BundleInfo:
        store = ReleaseStore(context.layout)
        with store.locked():
            state = store.load_state()
            if "package" in state.completed and context.layout.bundle_info.is_file():
                return store.load_bundle_info()
            if "site" not in state.completed:
                raise DeployExecutionError("release site has not been validated")
            report = store.load_build_report()
            release_bundler = bundler or ReleaseBundler(context.layout, store)
            try:
                bundle = release_bundler.package(context.spec, report)
                BundleVerifier().verify(
                    Path(bundle.bundle),
                    expected_sha256=bundle.bundle_sha256,
                )
                store.transition("packaged", completed_stage="package")
                return bundle
            except Exception as exc:
                store.transition("failed", error=str(exc))
                raise

    def publish(
        self,
        context: ReleaseContext,
        *,
        wait: bool = False,
        wait_timeout_seconds: float = 1800.0,
        dry_run: bool = False,
        force: bool = False,
        publisher: GitHubReleasePublisher | None = None,
    ) -> GitHubPublication:
        store = ReleaseStore(context.layout)
        with store.locked():
            state = store.load_state()
            if "package" not in state.completed:
                raise DeployExecutionError("release bundle has not been packaged")
            if (
                "publish" in state.completed
                and context.layout.publication.is_file()
                and not force
                and not dry_run
            ):
                existing = store.load_publication()
                if not wait or existing.status == "published":
                    return existing
            bundle = store.load_bundle_info()
            release_publisher = publisher or GitHubReleasePublisher(
                context.profile.publish
            )
            if dry_run:
                return release_publisher.publish(
                    bundle,
                    wait=wait,
                    wait_timeout_seconds=wait_timeout_seconds,
                    dry_run=True,
                )
            store.transition("uploading")
            try:
                publication = release_publisher.publish(
                    bundle,
                    wait=wait,
                    wait_timeout_seconds=wait_timeout_seconds,
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

    def deploy(
        self,
        profile_path: Path,
        *,
        only: Iterable[str] = (),
        options: ReleaseBuildOptions | None = None,
        publish: bool = True,
        wait: bool = False,
        wait_timeout_seconds: float = 1800.0,
        dry_run: bool = False,
        reuse: bool = True,
        fetch: bool = True,
    ) -> ReleaseDeploymentResult:
        context = self.plan(
            profile_path,
            only=only,
            reuse=reuse,
            persist=not dry_run,
            fetch=fetch and not dry_run,
        )
        if dry_run:
            return ReleaseDeploymentResult(context)
        report = self.build(context, options=options)
        bundle = self.package(context)
        publication = (
            self.publish(
                context,
                wait=wait,
                wait_timeout_seconds=wait_timeout_seconds,
            )
            if publish
            else None
        )
        refreshed = self.context(context.spec.release_id)
        return ReleaseDeploymentResult(refreshed, report, bundle, publication)


__all__ = [
    "ReleaseContext",
    "ReleaseDeploymentResult",
    "StaticReleaseService",
]
