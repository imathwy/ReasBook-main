"""GitHub Release storage and Pages workflow publication adapter."""

from __future__ import annotations

from dataclasses import dataclass
import hashlib
import json
import math
from pathlib import Path
import re
import time
from typing import TYPE_CHECKING, Any, Mapping
from urllib.error import HTTPError, URLError
from urllib.parse import quote, urlsplit
from urllib.request import Request, urlopen

from reasbook_sdk_common import CommandRunner

from ..errors import DeployConfigError, DeployExecutionError
from .github_client import (
    GITHUB_API_VERSION,
    GITHUB_JSON_ACCEPT,
    GitHubRepositoryClient,
)
from .models import GitHubPublishProfile
from .results import BundleInfo, ReleaseManifest, ReleaseSetManifest

if TYPE_CHECKING:
    from .bundle import BundleVerifier


_RELEASE_UPLOAD_TIMEOUT_SECONDS = 7200.0
_PAGES_HEALTH_MAX_BYTES = 1_000_000
_PAGES_HEALTH_POLL_SECONDS = 3.0


class _IncompleteDraftAssets(DeployExecutionError):
    def __init__(self, assets: tuple[tuple[int, str], ...]) -> None:
        super().__init__("draft GitHub Release contains incomplete uploads")
        self.assets = assets


def _sha256_file(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        while chunk := handle.read(1024 * 1024):
            digest.update(chunk)
    return digest.hexdigest()


@dataclass(frozen=True)
class GitHubPublication:
    release_id: str
    repository: str
    tag: str
    workflow: str
    status: str
    run_id: int | None = None
    pages_release_spec_url: str | None = None

    def __post_init__(self) -> None:
        if self.status not in {"planned", "dispatched", "published"}:
            raise DeployExecutionError(
                f"invalid GitHub publication status: {self.status}"
            )
        if self.status == "published":
            if self.run_id is None or self.pages_release_spec_url is None:
                raise DeployExecutionError(
                    "published GitHub Pages evidence requires a run and health URL"
                )
            parsed = urlsplit(self.pages_release_spec_url)
            if (
                parsed.scheme != "https"
                or not parsed.hostname
                or parsed.username is not None
                or parsed.password is not None
                or parsed.query
                or parsed.fragment
            ):
                raise DeployExecutionError(
                    "published GitHub Pages health URL is invalid"
                )
        elif self.pages_release_spec_url is not None:
            raise DeployExecutionError(
                "only a health-checked publication may record a Pages URL"
            )

    def public_dict(self) -> dict[str, Any]:
        return {
            "release_id": self.release_id,
            "repository": self.repository,
            "tag": self.tag,
            "workflow": self.workflow,
            "status": self.status,
            "run_id": self.run_id,
            "pages_release_spec_url": self.pages_release_spec_url,
        }

    @classmethod
    def from_dict(cls, value: dict[str, Any]) -> "GitHubPublication":
        try:
            return cls(
                release_id=str(value["release_id"]),
                repository=str(value["repository"]),
                tag=str(value["tag"]),
                workflow=str(value["workflow"]),
                status=str(value["status"]),
                run_id=int(value["run_id"]) if value.get("run_id") else None,
                pages_release_spec_url=(
                    str(value["pages_release_spec_url"])
                    if value.get("pages_release_spec_url")
                    else None
                ),
            )
        except (KeyError, TypeError, ValueError) as exc:
            raise DeployExecutionError(
                f"invalid GitHub publication record: {exc}"
            ) from exc


class GitHubReleasePublisher(GitHubRepositoryClient):
    """Upload a verified Pages bundle, then dispatch a publish-only workflow."""

    def __init__(
        self,
        profile: GitHubPublishProfile,
        *,
        runner: CommandRunner | None = None,
        repo_root: Path | None = None,
        expected_base_path: str | None = None,
        expected_spec_digest: str | None = None,
        expected_artifact_policy_sha256: str | None = None,
        expected_registry_commit: str | None = None,
        expected_tooling_revision: str | None = None,
        expected_release_set_sha256: str | None = None,
        bundle_verifier: BundleVerifier | None = None,
    ) -> None:
        super().__init__(profile, runner=runner, repo_root=repo_root)
        self.expected_base_path = expected_base_path
        self.expected_spec_digest = expected_spec_digest
        self.expected_artifact_policy_sha256 = expected_artifact_policy_sha256
        self.expected_registry_commit = expected_registry_commit
        self.expected_tooling_revision = expected_tooling_revision
        self.expected_release_set_sha256 = expected_release_set_sha256
        if bundle_verifier is None:
            # Keep github -> bundle lazy: bundle -> store -> github is part of
            # the persisted-publication model and must remain importable.
            from .bundle import BundleVerifier

            bundle_verifier = BundleVerifier()
        self.bundle_verifier = bundle_verifier

    def publish(
        self,
        bundle: BundleInfo,
        *,
        wait: bool = False,
        wait_timeout_seconds: float = 1800.0,
        pages_health_timeout_seconds: float = 300.0,
        dry_run: bool = False,
    ) -> GitHubPublication:
        from .bundle import normalize_sha256

        if not math.isfinite(wait_timeout_seconds) or wait_timeout_seconds <= 0:
            raise DeployExecutionError("wait timeout must be positive")
        if (
            not math.isfinite(pages_health_timeout_seconds)
            or pages_health_timeout_seconds <= 0
        ):
            raise DeployExecutionError("Pages health timeout must be positive")
        assets = tuple(
            Path(value).expanduser().resolve()
            for value in (
                bundle.bundle,
                bundle.manifest,
                bundle.checksums,
                *((bundle.release_set,) if bundle.release_set else ()),
            )
        )
        for asset in assets:
            if not asset.is_file() or asset.is_symlink():
                raise DeployExecutionError(f"release asset does not exist: {asset}")
        frozen_assets = self._snapshot_assets(assets)
        if bundle.artifact != "pages":
            raise DeployExecutionError(
                "GitHub Pages publication requires the pages artifact"
            )
        expected_release_set_sha256 = normalize_sha256(self.expected_release_set_sha256)
        if expected_release_set_sha256 is None:
            raise DeployExecutionError(
                "GitHub publication requires the accepted ReleaseSet checksum"
            )
        self._validate_assets(
            bundle,
            assets,
            expected_base_path=self.expected_base_path,
            expected_spec_digest=self.expected_spec_digest,
            expected_artifact_policy_sha256=(self.expected_artifact_policy_sha256),
            expected_release_set_sha256=expected_release_set_sha256,
        )
        self._require_external_manifest_matches_bundle(bundle, assets[1])
        self._require_local_assets_unchanged(assets, frozen_assets)
        tag = (
            f"{self.profile.release_tag_prefix}-"
            f"{bundle.release_id.removeprefix('site-')}"
        )
        expected_registry_commit = self._release_registry_commit()
        self._require_publishable_tooling_revision(expected_registry_commit)
        self._require_immutable_releases_enabled()
        if dry_run:
            return GitHubPublication(
                bundle.release_id,
                self.profile.repository,
                tag,
                self.profile.workflow,
                "planned",
            )

        existing_release = self._release_by_tag(tag)
        release_created = False
        workflow_ref: str | None = None
        if existing_release is None:
            workflow_ref = self._default_branch()
            trusted_sha = self._trusted_target(workflow_ref)
            self._require_registry_target(
                expected_registry_commit,
                trusted_sha,
                boundary="GitHub default branch",
            )
            self._ensure_tag_target(tag, expected_registry_commit)
            existing_release, release_created = self._create_draft_release(
                tag,
                expected_registry_commit,
                bundle.release_id,
            )
            self._require_registry_target(
                expected_registry_commit,
                self._tag_target(tag),
                boundary="new release tag",
            )
        else:
            tag_target = self._tag_target(tag)
            self._require_registry_target(
                expected_registry_commit,
                tag_target,
                boundary="immutable release tag",
            )

        release_is_draft = existing_release.get("draft")
        if not isinstance(release_is_draft, bool):
            raise DeployExecutionError("existing release has invalid draft metadata")
        release_database_id = self._release_database_id(existing_release)
        if existing_release.get("tag_name") != tag:
            raise DeployExecutionError(
                "GitHub Release does not match the requested tag"
            )
        if not release_is_draft and existing_release.get("immutable") is not True:
            raise DeployExecutionError(
                "existing published GitHub Release is not immutable"
            )
        if release_created:
            self._require_local_assets_unchanged(assets, frozen_assets)
            self._run(
                "release",
                "upload",
                tag,
                *(str(asset) for asset in assets),
                "--repo",
                self.profile.repository,
                timeout_seconds=_RELEASE_UPLOAD_TIMEOUT_SECONDS,
            )
        else:
            try:
                missing = self._validate_existing_release(
                    existing_release,
                    assets,
                    frozen_assets,
                )
            except _IncompleteDraftAssets:
                existing_release, missing = self._recover_incomplete_draft_assets(
                    tag,
                    existing_release,
                    assets,
                    frozen_assets,
                )
            if missing:
                self._require_local_assets_unchanged(assets, frozen_assets)
                self._run(
                    "release",
                    "upload",
                    tag,
                    *(str(asset) for asset in missing),
                    "--repo",
                    self.profile.repository,
                    timeout_seconds=_RELEASE_UPLOAD_TIMEOUT_SECONDS,
                )
        self._require_local_assets_unchanged(assets, frozen_assets)
        if release_is_draft:
            # The upload command returning success is not sufficient evidence
            # that GitHub has attached every immutable asset. Re-read the
            # release, bind it to the same draft identity, and validate all
            # names, sizes, and server-computed digests before publishing it.
            existing_release = self._wait_for_complete_draft_assets(
                tag,
                existing_release,
                assets,
                frozen_assets,
            )
        self._require_registry_target(
            expected_registry_commit,
            self._tag_target(tag),
            boundary="release tag before publication",
        )
        # Uploading to a draft remains recoverable. Recheck immediately before
        # the release becomes immutable and before any Pages dispatch, rather
        # than trusting a potentially stale pre-upload setting.
        self._require_immutable_releases_enabled()
        if release_is_draft:
            self._publish_draft_release(existing_release)
        immutable_release = self._wait_for_immutable_release(tag)
        if (
            immutable_release.get("tag_name") != tag
            or immutable_release.get("draft") is not False
            or self._release_database_id(immutable_release) != release_database_id
        ):
            raise DeployExecutionError(
                "immutable GitHub Release identity changed before dispatch"
            )
        if self._validate_existing_release(
            immutable_release,
            assets,
            frozen_assets,
        ):
            raise DeployExecutionError(
                "immutable GitHub Release assets are incomplete before dispatch"
            )
        previous_runs = self._workflow_run_ids() if wait else set()
        if workflow_ref is None:
            workflow_ref = self._default_branch()
        self._require_registry_target(
            expected_registry_commit,
            self._tag_target(tag),
            boundary="published release tag",
        )
        self._run(
            "workflow",
            "run",
            self.profile.workflow,
            "--repo",
            self.profile.repository,
            "--ref",
            workflow_ref,
            "-f",
            f"release_tag={tag}",
        )
        if not wait:
            return GitHubPublication(
                bundle.release_id,
                self.profile.repository,
                tag,
                self.profile.workflow,
                "dispatched",
            )
        run_id = self._wait_for_pages(
            tag,
            wait_timeout_seconds,
            previous_runs=previous_runs,
        )
        pages_release_spec_url = self._wait_for_public_pages(
            bundle.release_id,
            expected_spec_digest=self.expected_spec_digest,
            expected_registry_commit=expected_registry_commit,
            timeout=pages_health_timeout_seconds,
        )
        return GitHubPublication(
            bundle.release_id,
            self.profile.repository,
            tag,
            self.profile.workflow,
            "published",
            run_id,
            pages_release_spec_url,
        )

    def _release_registry_commit(self) -> str:
        commit = self.expected_registry_commit
        if commit is None or not re.fullmatch(r"[0-9a-f]{40}", commit):
            raise DeployExecutionError(
                "GitHub publication requires the ReleaseSpec registry commit"
            )
        return commit

    def _require_external_manifest_matches_bundle(
        self,
        bundle: BundleInfo,
        external_manifest: Path,
    ) -> None:
        try:
            external_bytes = external_manifest.read_bytes()
            embedded_bytes = self.bundle_verifier.release_manifest_bytes(
                Path(bundle.bundle),
                expected_sha256=bundle.bundle_sha256,
            )
            external_value = json.loads(external_bytes)
            embedded_value = json.loads(embedded_bytes)
            if not isinstance(external_value, dict) or not isinstance(
                embedded_value,
                dict,
            ):
                raise DeployConfigError("release manifests must be objects")
            external = ReleaseManifest.from_dict(external_value)
            embedded = ReleaseManifest.from_dict(embedded_value)
        except (OSError, UnicodeError, json.JSONDecodeError, DeployConfigError) as exc:
            raise DeployExecutionError(
                "cannot compare external and bundled release manifests"
            ) from exc
        if external_bytes != embedded_bytes or external != embedded:
            raise DeployExecutionError(
                "external release manifest differs from the bundled manifest"
            )

    def _require_publishable_tooling_revision(self, registry_commit: str) -> None:
        revision = self.expected_tooling_revision
        if revision is None or not re.fullmatch(
            re.escape(registry_commit) + r"\+tooling-sha256:[0-9a-f]{64}",
            revision,
        ):
            raise DeployExecutionError(
                "GitHub publication requires a clean tooling revision derived "
                "from the ReleaseSpec registry commit"
            )

    @staticmethod
    def _require_registry_target(
        registry_commit: str,
        target: str,
        *,
        boundary: str,
    ) -> None:
        if target != registry_commit:
            raise DeployExecutionError(
                f"ReleaseSpec registry commit does not match the {boundary}"
            )

    def _release_by_tag(self, tag: str) -> dict[str, Any] | None:
        """Return raw REST release metadata, treating only an explicit 404 as absent."""
        result = self._run(
            "api",
            f"repos/{self.profile.repository}/releases/tags/{tag}",
            "-H",
            f"Accept: {GITHUB_JSON_ACCEPT}",
            "-H",
            f"X-GitHub-Api-Version: {GITHUB_API_VERSION}",
            check=False,
        )
        if result.returncode != 0:
            detail = (result.stderr or result.stdout).strip()
            if re.search(r"(?:HTTP\s+404|\b404\s+Not Found\b)", detail, re.I):
                return None
            raise DeployExecutionError(
                "GitHub CLI release lookup failed" + (f": {detail}" if detail else "")
            )
        try:
            release = json.loads(result.stdout)
        except json.JSONDecodeError as exc:
            raise DeployExecutionError("GitHub returned invalid release JSON") from exc
        if not isinstance(release, dict):
            raise DeployExecutionError("GitHub release JSON must be an object")
        return release

    def _create_draft_release(
        self,
        tag: str,
        registry_commit: str,
        release_id: str,
    ) -> tuple[dict[str, Any], bool]:
        """Create through REST, or adopt an exact release won by a race.

        The repository's baseline GitHub CLI is 2.4, which predates
        ``gh release create --verify-tag``. The tag is already established and
        rechecked through the Git refs API, so using the Releases REST API also
        avoids a second, version-dependent tag-creation path.
        """

        result = self._run(
            "api",
            "--method",
            "POST",
            f"repos/{self.profile.repository}/releases",
            "--input",
            "-",
            "-H",
            f"Accept: {GITHUB_JSON_ACCEPT}",
            "-H",
            f"X-GitHub-Api-Version: {GITHUB_API_VERSION}",
            check=False,
            input_value={
                "tag_name": tag,
                "target_commitish": registry_commit,
                "name": f"ReasBook static site {release_id}",
                "body": (
                    "Immutable Pages artifact and ReleaseSet generated by "
                    "reasbook-deploy."
                ),
                "draft": True,
                "prerelease": False,
            },
        )
        if result.returncode != 0:
            detail = (result.stderr or result.stdout).strip()
            raced = self._release_by_tag(tag)
            if raced is None:
                raise DeployExecutionError(
                    "cannot create draft GitHub Release"
                    + (f": {detail}" if detail else "")
                )
            return raced, False
        try:
            release = json.loads(result.stdout)
        except json.JSONDecodeError as exc:
            raise DeployExecutionError(
                "GitHub returned invalid created-release JSON"
            ) from exc
        if (
            not isinstance(release, dict)
            or release.get("tag_name") != tag
            or release.get("draft") is not True
            or release.get("assets") != []
        ):
            raise DeployExecutionError(
                "GitHub returned incomplete created-release metadata"
            )
        self._release_database_id(release)
        return release, True

    def _publish_draft_release(self, release: dict[str, Any]) -> None:
        """Publish a draft without relying on the post-2.4 `gh release edit`."""

        release_id = self._release_database_id(release)
        self._run(
            "api",
            "--method",
            "PATCH",
            f"repos/{self.profile.repository}/releases/{release_id}",
            "--input",
            "-",
            "-H",
            f"Accept: {GITHUB_JSON_ACCEPT}",
            "-H",
            f"X-GitHub-Api-Version: {GITHUB_API_VERSION}",
            input_value={"draft": False},
        )

    def _wait_for_complete_draft_assets(
        self,
        tag: str,
        original_release: dict[str, Any],
        assets: tuple[Path, ...],
        expected_assets: Mapping[str, tuple[int, str]],
    ) -> dict[str, Any]:
        """Confirm upload convergence without crossing the immutable boundary."""

        expected_id = self._release_database_id(original_release)
        if original_release.get("draft") is not True:
            raise DeployExecutionError(
                "remote asset verification requires the original draft release"
            )
        if original_release.get("tag_name") != tag:
            raise DeployExecutionError(
                "draft GitHub Release does not match the requested tag"
            )

        for attempt in range(5):
            release = self._release_by_tag(tag)
            if release is None:
                raise DeployExecutionError(
                    "draft GitHub Release disappeared after asset upload"
                )
            if (
                release.get("draft") is not True
                or release.get("tag_name") != tag
                or self._release_database_id(release) != expected_id
            ):
                raise DeployExecutionError(
                    "draft GitHub Release identity changed after asset upload"
                )
            try:
                missing = self._validate_existing_release(
                    release,
                    assets,
                    expected_assets,
                )
            except _IncompleteDraftAssets:
                missing = assets
            if not missing:
                return release
            if attempt < 4:
                time.sleep(1.0)
        raise DeployExecutionError(
            "uploaded GitHub Release assets did not become complete"
        )

    def _recover_incomplete_draft_assets(
        self,
        tag: str,
        original_release: dict[str, Any],
        assets: tuple[Path, ...],
        expected_assets: Mapping[str, tuple[int, str]],
    ) -> tuple[dict[str, Any], tuple[Path, ...]]:
        """Delete only empty, expected-name ``starter`` assets before a retry."""

        expected_id = self._release_database_id(original_release)
        release = original_release
        pending: _IncompleteDraftAssets | None = None
        for attempt in range(5):
            self._require_draft_identity(release, tag, expected_id)
            try:
                return release, self._validate_existing_release(
                    release,
                    assets,
                    expected_assets,
                )
            except _IncompleteDraftAssets as exc:
                pending = exc
            if attempt < 4:
                time.sleep(1.0)
                refreshed = self._release_by_tag(tag)
                if refreshed is None:
                    raise DeployExecutionError(
                        "draft GitHub Release disappeared during upload recovery"
                    )
                release = refreshed

        assert pending is not None
        for asset_id, _name in pending.assets:
            self._run(
                "api",
                "--method",
                "DELETE",
                f"repos/{self.profile.repository}/releases/assets/{asset_id}",
            )

        for attempt in range(5):
            refreshed = self._release_by_tag(tag)
            if refreshed is None:
                raise DeployExecutionError(
                    "draft GitHub Release disappeared after upload cleanup"
                )
            self._require_draft_identity(refreshed, tag, expected_id)
            try:
                return refreshed, self._validate_existing_release(
                    refreshed,
                    assets,
                    expected_assets,
                )
            except _IncompleteDraftAssets:
                if attempt < 4:
                    time.sleep(1.0)
        raise DeployExecutionError(
            "incomplete GitHub Release assets did not clear for retry"
        )

    @staticmethod
    def _require_draft_identity(
        release: dict[str, Any],
        tag: str,
        expected_id: int,
    ) -> None:
        if (
            release.get("draft") is not True
            or release.get("tag_name") != tag
            or GitHubReleasePublisher._release_database_id(release) != expected_id
        ):
            raise DeployExecutionError(
                "draft GitHub Release identity changed during upload recovery"
            )

    @staticmethod
    def _snapshot_assets(
        assets: tuple[Path, ...],
    ) -> dict[str, tuple[int, str]]:
        return {
            asset.name: (asset.stat().st_size, f"sha256:{_sha256_file(asset)}")
            for asset in assets
        }

    @staticmethod
    def _require_local_assets_unchanged(
        assets: tuple[Path, ...],
        expected: Mapping[str, tuple[int, str]],
    ) -> None:
        if GitHubReleasePublisher._snapshot_assets(assets) != expected:
            raise DeployExecutionError(
                "release assets changed after publication validation"
            )

    @staticmethod
    def _release_database_id(release: dict[str, Any]) -> int:
        release_id = release.get("id")
        if (
            isinstance(release_id, bool)
            or not isinstance(release_id, int)
            or release_id < 1
        ):
            raise DeployExecutionError("GitHub Release has an invalid database ID")
        return release_id

    def _wait_for_immutable_release(self, tag: str) -> dict[str, Any]:
        """Wait within a bounded window for the immutable flag to converge."""

        # Immutable-release attestations are created asynchronously. Match the
        # workflow's bounded convergence window so a healthy large upload does
        # not require an operator to rerun the otherwise one-click path.
        for attempt in range(12):
            release = self._release_by_tag(tag)
            if release is None:
                raise DeployExecutionError(
                    "published GitHub Release disappeared before dispatch"
                )
            immutable = release.get("immutable")
            if immutable is True:
                return release
            if immutable is not False:
                raise DeployExecutionError(
                    "GitHub Release response has invalid immutable metadata"
                )
            if attempt < 11:
                time.sleep(5.0)
        raise DeployExecutionError(
            "GitHub Release did not become immutable before Pages dispatch"
        )

    def _tag_target(self, tag: str) -> str:
        target = self._optional_tag_target(tag)
        if target is None:
            raise DeployExecutionError("release tag is missing")
        return target

    def _optional_tag_target(self, tag: str) -> str | None:
        result = self._run(
            "api",
            f"repos/{self.profile.repository}/git/ref/tags/{tag}",
            check=False,
        )
        if result.returncode != 0:
            detail = (result.stderr or result.stdout).strip()
            if re.search(r"(?:HTTP\s+404|\b404\s+Not Found\b)", detail, re.I):
                return None
            raise DeployExecutionError(
                "GitHub CLI release-tag lookup failed"
                + (f": {detail}" if detail else "")
            )
        try:
            value = json.loads(result.stdout)
            target_type = str(value["object"]["type"])
            target = str(value["object"]["sha"])
        except (KeyError, TypeError, json.JSONDecodeError) as exc:
            raise DeployExecutionError(
                "GitHub returned invalid release-tag JSON"
            ) from exc
        # Match the workflow boundary: accept at most four annotated tag
        # objects before the final commit.
        for _ in range(5):
            if target_type == "commit":
                if not re.fullmatch(r"[0-9a-f]{40}", target):
                    break
                return target
            if target_type != "tag" or not re.fullmatch(r"[0-9a-f]{40}", target):
                break
            result = self._run(
                "api", f"repos/{self.profile.repository}/git/tags/{target}"
            )
            try:
                value = json.loads(result.stdout)
                target_type = str(value["object"]["type"])
                target = str(value["object"]["sha"])
            except (KeyError, TypeError, json.JSONDecodeError) as exc:
                raise DeployExecutionError(
                    "GitHub returned invalid annotated-tag JSON"
                ) from exc
        raise DeployExecutionError("release tag does not resolve to a commit")

    def _ensure_tag_target(self, tag: str, registry_commit: str) -> None:
        """Atomically establish a tag at the exact release commit.

        The Releases API ignores ``target_commitish`` when a tag already
        exists.  Creating the Git ref first makes that case explicit, and a
        failed create is accepted only when a concurrent creator installed the
        exact same target.
        """

        target = self._optional_tag_target(tag)
        if target is not None:
            self._require_registry_target(
                registry_commit,
                target,
                boundary="pre-existing release tag",
            )
            return

        endpoint = f"repos/{self.profile.repository}/git/refs"
        result = self._run(
            "api",
            "--method",
            "POST",
            endpoint,
            "--input",
            "-",
            check=False,
            input_value={"ref": f"refs/tags/{tag}", "sha": registry_commit},
        )
        if result.returncode != 0:
            detail = (result.stderr or result.stdout).strip()
            raced_target = self._optional_tag_target(tag)
            if raced_target is None:
                raise DeployExecutionError(
                    "cannot create immutable release tag"
                    + (f": {detail}" if detail else "")
                )
            self._require_registry_target(
                registry_commit,
                raced_target,
                boundary="concurrently created release tag",
            )
            return

        self._require_registry_target(
            registry_commit,
            self._tag_target(tag),
            boundary="new release tag",
        )

    @staticmethod
    def _validate_assets(
        bundle: BundleInfo,
        assets: tuple[Path, ...],
        *,
        expected_base_path: str | None = None,
        expected_spec_digest: str | None = None,
        expected_artifact_policy_sha256: str | None = None,
        expected_release_set_sha256: str | None = None,
    ) -> None:
        if bundle.artifact == "pages" and not bundle.release_set:
            raise DeployExecutionError(
                "a Pages publication must include its release set"
            )
        bundle_name = (
            f"{bundle.release_id}.site.tar.zst"
            if bundle.artifact == "full"
            else f"{bundle.release_id}.{bundle.artifact}.site.tar.zst"
        )
        expected_names = (
            bundle_name,
            "release-manifest.json",
            "SHA256SUMS",
            *(("release-set.json",) if bundle.release_set else ()),
        )
        if tuple(asset.name for asset in assets) != expected_names:
            raise DeployExecutionError(
                "release assets must use the canonical bundle, manifest, "
                "and checksum names"
            )
        expected_digest = bundle.bundle_sha256.removeprefix("sha256:")
        if not re.fullmatch(r"[0-9a-f]{64}", expected_digest):
            raise DeployExecutionError("bundle has an invalid SHA256")
        digest = _sha256_file(assets[0])
        if digest != expected_digest:
            raise DeployExecutionError("bundle SHA256 does not match bundle metadata")
        if assets[2].read_text(encoding="utf-8") != (
            f"{expected_digest}  {assets[0].name}\n"
        ):
            raise DeployExecutionError("SHA256SUMS does not bind the canonical bundle")
        try:
            manifest_value = json.loads(assets[1].read_text(encoding="utf-8"))
            if not isinstance(manifest_value, dict):
                raise DeployConfigError("release manifest must be an object")
            manifest = ReleaseManifest.from_dict(manifest_value)
        except (OSError, DeployConfigError, json.JSONDecodeError) as exc:
            raise DeployExecutionError("release manifest is not valid JSON") from exc
        if (
            manifest.release_id != bundle.release_id
            or manifest.artifact != bundle.artifact
            or (
                expected_base_path is not None
                and manifest.base_path != expected_base_path
            )
            or (
                expected_spec_digest is not None
                and manifest.spec_digest != expected_spec_digest
            )
        ):
            raise DeployExecutionError(
                "release manifest does not match the expected Pages release"
            )
        if bundle.release_set:
            if (
                expected_release_set_sha256 is not None
                and _sha256_file(assets[3]) != expected_release_set_sha256
            ):
                raise DeployExecutionError(
                    "release set changed after required acceptance"
                )
            try:
                release_set_value = json.loads(assets[3].read_text(encoding="utf-8"))
                if not isinstance(release_set_value, dict):
                    raise DeployConfigError("release set must be an object")
                release_set = ReleaseSetManifest.from_dict(release_set_value)
                record = release_set.artifact(bundle.artifact)
            except (OSError, DeployConfigError, json.JSONDecodeError) as exc:
                raise DeployExecutionError("release set is invalid") from exc
            if (
                release_set.release_id != bundle.release_id
                or release_set.spec_digest != manifest.spec_digest
                or (
                    expected_artifact_policy_sha256 is not None
                    and release_set.artifact_policy_sha256
                    != expected_artifact_policy_sha256
                )
                or record.bundle != assets[0].name
                or record.bundle_sha256 != bundle.bundle_sha256
                or record.site_tree_sha256 != manifest.site_tree_sha256
                or record.file_count != manifest.file_count
                or record.total_bytes != manifest.total_bytes
            ):
                raise DeployExecutionError(
                    "release set does not bind the published artifact"
                )

    @staticmethod
    def _validate_existing_release(
        release: dict[str, Any],
        assets: tuple[Path, ...],
        expected: Mapping[str, tuple[int, str]],
    ) -> tuple[Path, ...]:
        if not isinstance(release.get("draft"), bool):
            raise DeployExecutionError("existing release has invalid draft metadata")
        remote_assets = release.get("assets")
        if not isinstance(remote_assets, list):
            raise DeployExecutionError("existing release has invalid asset metadata")
        if set(expected) != {asset.name for asset in assets}:
            raise DeployExecutionError("frozen release asset identity is incomplete")
        actual: dict[str, tuple[int, str]] = {}
        incomplete: list[tuple[int, str]] = []
        for item in remote_assets:
            if not isinstance(item, dict):
                raise DeployExecutionError(
                    "existing release has invalid asset metadata"
                )
            name = item.get("name")
            size = item.get("size")
            digest = item.get("digest")
            state = item.get("state")
            if (
                not isinstance(name, str)
                or not name
                or isinstance(size, bool)
                or not isinstance(size, int)
                or size < 0
                or name in actual
            ):
                raise DeployExecutionError(
                    "existing release has invalid asset metadata"
                )
            # GitHub documents a failed upstream upload as an empty asset in
            # the ``starter`` state.  That exact draft-only shape is the sole
            # remote asset we may delete automatically; an uploaded or
            # non-empty mismatch remains immutable/fail-closed.
            if state == "starter":
                asset_id = item.get("id")
                if (
                    release["draft"] is not True
                    or name not in expected
                    or isinstance(asset_id, bool)
                    or not isinstance(asset_id, int)
                    or asset_id < 1
                    or size != 0
                    or digest is not None
                ):
                    raise DeployExecutionError(
                        "existing release has invalid incomplete asset metadata"
                    )
                actual[name] = (size, "starter")
                incomplete.append((asset_id, name))
                continue
            if (
                state != "uploaded"
                or not isinstance(digest, str)
                or not re.fullmatch(r"sha256:[0-9a-f]{64}", digest)
            ):
                raise DeployExecutionError(
                    "existing release has invalid asset metadata"
                )
            actual[name] = (size, digest)
        if incomplete:
            raise _IncompleteDraftAssets(tuple(incomplete))
        mismatched = {
            name
            for name in actual.keys() & expected.keys()
            if actual[name] != expected[name]
        }
        extra = actual.keys() - expected.keys()
        if mismatched or extra:
            raise DeployExecutionError(
                "existing release assets differ; refusing to overwrite immutable assets"
            )
        missing_names = expected.keys() - actual.keys()
        if missing_names and not release["draft"]:
            raise DeployExecutionError(
                "published release is missing immutable assets; refusing to modify it"
            )
        return tuple(asset for asset in assets if asset.name in missing_names)

    def _workflow_run_ids(self) -> set[int]:
        return {run["id"] for run in self._workflow_runs()}

    def _workflow_runs(self) -> tuple[dict[str, Any], ...]:
        workflow = quote(self.profile.workflow, safe="")
        result = self._run(
            "api",
            f"repos/{self.profile.repository}/actions/workflows/"
            f"{workflow}/runs?event=workflow_dispatch&per_page=100",
            "-H",
            f"Accept: {GITHUB_JSON_ACCEPT}",
            "-H",
            f"X-GitHub-Api-Version: {GITHUB_API_VERSION}",
        )
        try:
            value = json.loads(result.stdout)
        except json.JSONDecodeError as exc:
            raise DeployExecutionError(
                "GitHub returned invalid workflow-runs JSON"
            ) from exc
        if not isinstance(value, dict) or not isinstance(
            value.get("workflow_runs"), list
        ):
            raise DeployExecutionError("GitHub workflow-runs response is incomplete")
        runs: list[dict[str, Any]] = []
        for run in value["workflow_runs"]:
            if not isinstance(run, dict):
                raise DeployExecutionError(
                    "GitHub workflow-runs response contains an invalid run"
                )
            run_id = run.get("id")
            display_title = run.get("display_title")
            status = run.get("status")
            conclusion = run.get("conclusion")
            if (
                isinstance(run_id, bool)
                or not isinstance(run_id, int)
                or run_id < 1
                or not isinstance(display_title, str)
                or not isinstance(status, str)
                or (conclusion is not None and not isinstance(conclusion, str))
            ):
                raise DeployExecutionError(
                    "GitHub workflow-runs response contains incomplete metadata"
                )
            runs.append(
                {
                    "id": run_id,
                    "display_title": display_title,
                    "status": status,
                    "conclusion": conclusion,
                }
            )
        return tuple(runs)

    def _public_pages_release_spec_url(self) -> str:
        base_path = self.expected_base_path
        if (
            not isinstance(base_path, str)
            or not base_path.startswith("/")
            or not base_path.endswith("/")
            or "//" in base_path
            or ".." in base_path
        ):
            raise DeployExecutionError(
                "GitHub Pages health verification requires a safe base path"
            )
        owner, repository = self.profile.repository.split("/", 1)
        if base_path != f"/{repository}/":
            raise DeployExecutionError(
                "GitHub Pages base path must match the repository name"
            )
        return f"https://{owner.lower()}.github.io" f"{base_path}release-spec.json"

    @staticmethod
    def _probe_public_pages(
        url: str,
        *,
        release_id: str,
        spec_digest: str,
        registry_commit: str,
        timeout: float,
    ) -> None:
        request = Request(url, headers={"User-Agent": "ReasBook-Release/1"})
        with urlopen(request, timeout=max(0.1, min(10.0, timeout))) as response:
            status = getattr(response, "status", None)
            if status != 200:
                raise DeployExecutionError(
                    f"public GitHub Pages health returned HTTP {status}"
                )
            final_url = response.geturl()
            if final_url != url:
                raise DeployExecutionError(
                    "public GitHub Pages health redirected outside its exact URL"
                )
            payload = response.read(_PAGES_HEALTH_MAX_BYTES + 1)
        if len(payload) > _PAGES_HEALTH_MAX_BYTES:
            raise DeployExecutionError(
                "public GitHub Pages ReleaseSpec exceeds its safety limit"
            )
        try:
            value = json.loads(payload.decode("utf-8"))
        except (UnicodeError, json.JSONDecodeError) as exc:
            raise DeployExecutionError(
                "public GitHub Pages health is not valid JSON"
            ) from exc
        source = value.get("source") if isinstance(value, dict) else None
        if (
            not isinstance(source, dict)
            or value.get("release_id") != release_id
            or value.get("spec_digest") != spec_digest
            or source.get("registry_commit") != registry_commit
        ):
            raise DeployExecutionError(
                "public GitHub Pages health reports another release"
            )

    def _wait_for_public_pages(
        self,
        release_id: str,
        *,
        expected_spec_digest: str | None,
        expected_registry_commit: str,
        timeout: float,
    ) -> str:
        if not isinstance(expected_spec_digest, str) or not re.fullmatch(
            r"sha256:[0-9a-f]{64}", expected_spec_digest
        ):
            raise DeployExecutionError(
                "GitHub Pages health verification requires the ReleaseSpec digest"
            )
        url = self._public_pages_release_spec_url()
        deadline = time.monotonic() + timeout
        last_error = "the public URL has not converged"
        while time.monotonic() < deadline:
            remaining = deadline - time.monotonic()
            try:
                self._probe_public_pages(
                    url,
                    release_id=release_id,
                    spec_digest=expected_spec_digest,
                    registry_commit=expected_registry_commit,
                    timeout=remaining,
                )
                return url
            except (
                HTTPError,
                URLError,
                OSError,
                DeployExecutionError,
            ) as exc:
                last_error = str(exc)
            remaining = deadline - time.monotonic()
            if remaining > 0:
                time.sleep(min(_PAGES_HEALTH_POLL_SECONDS, remaining))
        raise DeployExecutionError(
            "timed out waiting for public GitHub Pages ReleaseSpec convergence: "
            f"{last_error}"
        )

    def _wait_for_pages(
        self,
        tag: str,
        timeout: float,
        *,
        previous_runs: set[int],
    ) -> int:
        deadline = time.monotonic() + timeout
        title = f"Publish {tag}"
        while time.monotonic() < deadline:
            for run in self._workflow_runs():
                if run["display_title"] != title:
                    continue
                run_id = run["id"]
                if run_id in previous_runs:
                    continue
                status = run["status"]
                if status != "completed":
                    break
                if run["conclusion"] != "success":
                    raise DeployExecutionError(
                        f"Pages workflow failed: {run['conclusion']}"
                    )
                return run_id
            time.sleep(3)
        raise DeployExecutionError(f"timed out waiting for Pages workflow for {tag}")


__all__ = [
    "GitHubPublication",
    "GitHubReleasePublisher",
]
