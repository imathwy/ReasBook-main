"""GitHub Release storage and Pages workflow publication adapter."""

from __future__ import annotations

from dataclasses import dataclass
import hashlib
import json
import math
from pathlib import Path
import re
import time
from typing import Any

from reasbook_sdk_common import CommandRunner

from ..errors import DeployConfigError, DeployExecutionError
from .github_client import GitHubRepositoryClient
from .models import GitHubPublishProfile
from .results import BundleInfo, ReleaseManifest, ReleaseSetManifest


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

    def __post_init__(self) -> None:
        if self.status not in {"planned", "dispatched", "published"}:
            raise DeployExecutionError(
                f"invalid GitHub publication status: {self.status}"
            )

    def public_dict(self) -> dict[str, Any]:
        return {
            "release_id": self.release_id,
            "repository": self.repository,
            "tag": self.tag,
            "workflow": self.workflow,
            "status": self.status,
            "run_id": self.run_id,
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
    ) -> None:
        super().__init__(profile, runner=runner, repo_root=repo_root)
        self.expected_base_path = expected_base_path
        self.expected_spec_digest = expected_spec_digest
        self.expected_artifact_policy_sha256 = expected_artifact_policy_sha256

    def publish(
        self,
        bundle: BundleInfo,
        *,
        wait: bool = False,
        wait_timeout_seconds: float = 1800.0,
        dry_run: bool = False,
    ) -> GitHubPublication:
        if not math.isfinite(wait_timeout_seconds) or wait_timeout_seconds <= 0:
            raise DeployExecutionError("wait timeout must be positive")
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
        if bundle.artifact != "pages":
            raise DeployExecutionError(
                "GitHub Pages publication requires the pages artifact"
            )
        self._validate_assets(
            bundle,
            assets,
            expected_base_path=self.expected_base_path,
            expected_spec_digest=self.expected_spec_digest,
            expected_artifact_policy_sha256=(
                self.expected_artifact_policy_sha256
            ),
        )
        tag = (
            f"{self.profile.release_tag_prefix}-"
            f"{bundle.release_id.removeprefix('site-')}"
        )
        if dry_run:
            return GitHubPublication(
                bundle.release_id,
                self.profile.repository,
                tag,
                self.profile.workflow,
                "planned",
            )

        existing_release = self._release_by_tag(tag)
        workflow_ref: str | None = None
        if existing_release is None:
            workflow_ref = self._default_branch()
            trusted_sha = self._trusted_target(workflow_ref)
            self._run(
                "release",
                "create",
                tag,
                "--repo",
                self.profile.repository,
                "--target",
                trusted_sha,
                "--draft",
                "--title",
                f"ReasBook static site {bundle.release_id}",
                "--notes",
                "Immutable Pages artifact and ReleaseSet generated by "
                "reasbook-deploy.",
            )
            self._run(
                "release",
                "upload",
                tag,
                *(str(asset) for asset in assets),
                "--repo",
                self.profile.repository,
            )
        else:
            tag_target = self._tag_target(tag)
            missing = self._validate_existing_release(
                existing_release, assets, tag_target
            )
            if missing:
                self._run(
                    "release",
                    "upload",
                    tag,
                    *(str(asset) for asset in missing),
                    "--repo",
                    self.profile.repository,
                )
        self._run(
            "release",
            "edit",
            tag,
            "--repo",
            self.profile.repository,
            "--draft=false",
        )
        previous_runs = self._workflow_run_ids() if wait else set()
        if workflow_ref is None:
            workflow_ref = self._default_branch()
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
        return GitHubPublication(
            bundle.release_id,
            self.profile.repository,
            tag,
            self.profile.workflow,
            "published",
            run_id,
        )

    def _release_by_tag(self, tag: str) -> dict[str, Any] | None:
        """Return raw REST release metadata, treating only an explicit 404 as absent."""
        result = self._run(
            "api",
            f"repos/{self.profile.repository}/releases/tags/{tag}",
            check=False,
        )
        if result.returncode != 0:
            detail = (result.stderr or result.stdout).strip()
            if re.search(r"(?:HTTP\s+404|\b404\s+Not Found\b)", detail, re.I):
                return None
            raise DeployExecutionError(
                "GitHub CLI release lookup failed"
                + (f": {detail}" if detail else "")
            )
        try:
            release = json.loads(result.stdout)
        except json.JSONDecodeError as exc:
            raise DeployExecutionError("GitHub returned invalid release JSON") from exc
        if not isinstance(release, dict):
            raise DeployExecutionError("GitHub release JSON must be an object")
        return release

    def _tag_target(self, tag: str) -> str:
        result = self._run(
            "api", f"repos/{self.profile.repository}/git/ref/tags/{tag}"
        )
        try:
            value = json.loads(result.stdout)
            target_type = str(value["object"]["type"])
            target = str(value["object"]["sha"])
        except (KeyError, TypeError, json.JSONDecodeError) as exc:
            raise DeployExecutionError(
                "GitHub returned invalid release-tag JSON"
            ) from exc
        for _ in range(4):
            if target_type == "commit":
                if not re.fullmatch(r"[0-9a-f]{40}", target):
                    break
                return target
            if target_type != "tag" or not re.fullmatch(
                r"[0-9a-f]{40}", target
            ):
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

    @staticmethod
    def _validate_assets(
        bundle: BundleInfo,
        assets: tuple[Path, ...],
        *,
        expected_base_path: str | None = None,
        expected_spec_digest: str | None = None,
        expected_artifact_policy_sha256: str | None = None,
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
            try:
                release_set_value = json.loads(
                    assets[3].read_text(encoding="utf-8")
                )
                if not isinstance(release_set_value, dict):
                    raise DeployConfigError("release set must be an object")
                release_set = ReleaseSetManifest.from_dict(release_set_value)
                record = release_set.artifact(bundle.artifact)
            except (OSError, DeployConfigError, json.JSONDecodeError) as exc:
                raise DeployExecutionError(
                    "release set is invalid"
                ) from exc
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
        tag_target: str,
    ) -> tuple[Path, ...]:
        if release.get("target_commitish") != tag_target:
            raise DeployExecutionError(
                "existing release target does not match its immutable tag"
            )
        if not isinstance(release.get("draft"), bool):
            raise DeployExecutionError("existing release has invalid draft metadata")
        remote_assets = release.get("assets")
        if not isinstance(remote_assets, list):
            raise DeployExecutionError("existing release has invalid asset metadata")
        expected = {
            asset.name: (asset.stat().st_size, f"sha256:{_sha256_file(asset)}")
            for asset in assets
        }
        actual: dict[str, tuple[int, str]] = {}
        for item in remote_assets:
            if not isinstance(item, dict):
                raise DeployExecutionError("existing release has invalid asset metadata")
            name = item.get("name")
            size = item.get("size")
            digest = item.get("digest")
            if (
                not isinstance(name, str)
                or not name
                or isinstance(size, bool)
                or not isinstance(size, int)
                or size < 0
                or not isinstance(digest, str)
                or not re.fullmatch(r"sha256:[0-9a-f]{64}", digest)
                or name in actual
            ):
                raise DeployExecutionError("existing release has invalid asset metadata")
            actual[name] = (size, digest)
        mismatched = {
            name for name in actual.keys() & expected.keys() if actual[name] != expected[name]
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
        result = self._run(
            "run",
            "list",
            "--repo",
            self.profile.repository,
            "--workflow",
            self.profile.workflow,
            "--limit",
            "20",
            "--json",
            "databaseId",
        )
        try:
            runs = json.loads(result.stdout)
        except json.JSONDecodeError as exc:
            raise DeployExecutionError(
                "GitHub CLI returned invalid workflow JSON"
            ) from exc
        if not isinstance(runs, list):
            raise DeployExecutionError("GitHub CLI workflow JSON must be an array")
        return {
            int(run["databaseId"])
            for run in runs
            if isinstance(run, dict) and run.get("databaseId") is not None
        }

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
            result = self._run(
                "run",
                "list",
                "--repo",
                self.profile.repository,
                "--workflow",
                self.profile.workflow,
                "--limit",
                "20",
                "--json",
                "databaseId,displayTitle,status,conclusion",
            )
            try:
                runs = json.loads(result.stdout)
            except json.JSONDecodeError as exc:
                raise DeployExecutionError(
                    "GitHub CLI returned invalid workflow JSON"
                ) from exc
            for run in runs if isinstance(runs, list) else ():
                if not isinstance(run, dict) or run.get("displayTitle") != title:
                    continue
                run_id = int(run["databaseId"])
                if run_id in previous_runs:
                    continue
                status = run.get("status")
                if status != "completed":
                    break
                if run.get("conclusion") != "success":
                    raise DeployExecutionError(
                        f"Pages workflow failed: {run.get('conclusion')}"
                    )
                return run_id
            time.sleep(3)
        raise DeployExecutionError(f"timed out waiting for Pages workflow for {tag}")

__all__ = [
    "GitHubPublication",
    "GitHubReleasePublisher",
]
