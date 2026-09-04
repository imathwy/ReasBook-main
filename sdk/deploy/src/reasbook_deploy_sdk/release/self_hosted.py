"""Fail-closed installation of verified bundles on a static-site server."""

from __future__ import annotations

from contextlib import contextmanager
from dataclasses import dataclass
import fcntl
import json
import os
from pathlib import Path
import shutil
import time
from typing import Iterator
from urllib.error import URLError
from urllib.parse import urlsplit
from urllib.request import urlopen
import uuid

from reasbook_sdk_common import atomic_write_json

from ..errors import DeployConfigError, DeployExecutionError
from .bundle import BundleVerifier, normalize_sha256, site_tree_digest
from .models import ARTIFACT_NAME_RE, RELEASE_ID_RE
from .results import ReleaseManifest, ReleaseSetManifest


@dataclass(frozen=True)
class SelfHostedDeployment:
    release_id: str
    artifact: str
    deployment_root: str
    active_site: str
    previous_release_id: str | None
    status: str = "active"

    def public_dict(self) -> dict[str, str | None]:
        return {
            "release_id": self.release_id,
            "artifact": self.artifact,
            "deployment_root": self.deployment_root,
            "active_site": self.active_site,
            "previous_release_id": self.previous_release_id,
            "status": self.status,
        }


class SelfHostedInstaller:
    """Install, activate, and roll back immutable release directories."""

    def __init__(
        self,
        deployment_root: Path,
        *,
        verifier: BundleVerifier | None = None,
    ) -> None:
        raw = Path(deployment_root).expanduser()
        if raw.is_symlink():
            raise DeployConfigError("self-hosted deployment root must not be a symlink")
        root = raw.resolve(strict=False)
        if root in {Path("/"), Path.home().resolve()}:
            raise DeployConfigError(f"refusing broad deployment root: {root}")
        self.root = root
        self.verifier = verifier or BundleVerifier()

    def install(
        self,
        bundle: Path,
        *,
        release_set: Path,
        expected_artifact_policy_sha256: str,
        expected_sha256: str,
        artifact: str = "full",
        health_url: str | None = None,
        filesystem_health_only: bool = False,
        health_attempts: int = 20,
        health_interval_seconds: float = 1.0,
    ) -> SelfHostedDeployment:
        self._validate_options(
            artifact,
            health_attempts,
            health_interval_seconds,
            health_url=health_url,
            filesystem_health_only=filesystem_health_only,
        )
        archive = Path(bundle).expanduser().resolve()
        expected = normalize_sha256(expected_sha256)
        assert expected is not None
        manifest = self.verifier.inspect(
            archive,
            expected_sha256=expected,
        )
        if manifest.artifact != artifact:
            raise DeployExecutionError(
                f"bundle contains {manifest.artifact}, expected {artifact}"
            )
        release_set_value = self._load_release_set(Path(release_set))
        record = release_set_value.artifact(artifact)
        record_digest = normalize_sha256(record.bundle_sha256)
        assert record_digest is not None
        if expected != record_digest:
            raise DeployExecutionError(
                "expected bundle checksum does not match the ReleaseSet"
            )
        self._validate_release_set_binding(
            release_set_value,
            manifest,
            expected_artifact_policy_sha256=expected_artifact_policy_sha256,
        )
        self._prepare_root()
        self._require_capacity(manifest)

        with self._locked():
            target = self._target(manifest.release_id, artifact)
            if target.is_dir():
                installed = self._load_installed_manifest(target)
                if installed != manifest:
                    raise DeployExecutionError(
                        "installed release differs from the requested bundle"
                    )
                installed_release_set = self._load_release_set(
                    target / "release-set.json"
                )
                if installed_release_set != release_set_value:
                    raise DeployExecutionError(
                        "installed ReleaseSet differs from the requested ReleaseSet"
                    )
                self._verify_installed(
                    target,
                    manifest,
                    installed_release_set,
                    expected_artifact_policy_sha256=(
                        expected_artifact_policy_sha256
                    ),
                )
            elif target.exists():
                raise DeployExecutionError(
                    f"self-hosted release target is not a directory: {target}"
                )
            else:
                self._install_new(
                    archive,
                    target,
                    manifest,
                    release_set_value,
                    record_digest,
                )

            previous = self._active_release_id()
            if self._active_target() != target:
                previous_link = self._current_link_value()
                try:
                    self._replace_current(target)
                    self._probe(
                        manifest,
                        health_url=health_url,
                        filesystem_health_only=filesystem_health_only,
                        attempts=health_attempts,
                        interval=health_interval_seconds,
                    )
                # CLI signal handlers raise SystemExit.  Treat it like every
                # other failed health check so an interrupted activation never
                # leaves an unverified release active.
                except BaseException:
                    self._restore_current(previous_link)
                    raise
            else:
                self._probe(
                    manifest,
                    health_url=health_url,
                    filesystem_health_only=filesystem_health_only,
                    attempts=health_attempts,
                    interval=health_interval_seconds,
                )
            return SelfHostedDeployment(
                release_id=manifest.release_id,
                artifact=artifact,
                deployment_root=str(self.root),
                active_site=str(self._public_site(target, manifest)),
                previous_release_id=(
                    previous if previous != manifest.release_id else None
                ),
            )

    def rollback(
        self,
        release_id: str,
        *,
        artifact: str = "full",
        health_url: str | None = None,
        filesystem_health_only: bool = False,
        expected_artifact_policy_sha256: str | None = None,
        health_attempts: int = 20,
        health_interval_seconds: float = 1.0,
    ) -> SelfHostedDeployment:
        self._validate_options(
            artifact,
            health_attempts,
            health_interval_seconds,
            health_url=health_url,
            filesystem_health_only=filesystem_health_only,
        )
        if not RELEASE_ID_RE.fullmatch(release_id):
            raise DeployConfigError(f"invalid release ID: {release_id!r}")
        self._prepare_root()
        with self._locked():
            target = self._target(release_id, artifact)
            manifest = self._load_installed_manifest(target)
            release_set = self._load_release_set(target / "release-set.json")
            self._verify_installed(
                target,
                manifest,
                release_set,
                expected_artifact_policy_sha256=expected_artifact_policy_sha256,
            )
            previous = self._active_release_id()
            previous_link = self._current_link_value()
            try:
                self._replace_current(target)
                self._probe(
                    manifest,
                    health_url=health_url,
                    filesystem_health_only=filesystem_health_only,
                    attempts=health_attempts,
                    interval=health_interval_seconds,
                )
            # Preserve the transactional boundary for SIGINT/SIGTERM as well
            # as ordinary probe failures (see the matching install path).
            except BaseException:
                self._restore_current(previous_link)
                raise
            return SelfHostedDeployment(
                release_id=release_id,
                artifact=artifact,
                deployment_root=str(self.root),
                active_site=str(self._public_site(target, manifest)),
                previous_release_id=previous,
            )

    @staticmethod
    def _validate_options(
        artifact: str,
        attempts: int,
        interval: float,
        *,
        health_url: str | None,
        filesystem_health_only: bool,
    ) -> None:
        if not ARTIFACT_NAME_RE.fullmatch(artifact):
            raise DeployConfigError(f"invalid release artifact: {artifact!r}")
        if isinstance(attempts, bool) or attempts < 1 or interval <= 0:
            raise DeployConfigError("health-check settings must be positive")
        if not isinstance(filesystem_health_only, bool):
            raise DeployConfigError("filesystem health mode must be boolean")
        if bool(health_url) == filesystem_health_only:
            raise DeployConfigError(
                "select exactly one health mode: health_url or "
                "filesystem_health_only"
            )
        if health_url is not None:
            if (
                not isinstance(health_url, str)
                or not health_url
                or health_url != health_url.strip()
                or any(ord(character) <= 32 for character in health_url)
            ):
                raise DeployConfigError("health URL must be a valid HTTP(S) URL")
            try:
                parsed = urlsplit(health_url)
                _ = parsed.port
            except ValueError as exc:
                raise DeployConfigError(
                    "health URL must be a valid HTTP(S) URL"
                ) from exc
            if (
                parsed.scheme not in {"http", "https"}
                or parsed.hostname is None
                or parsed.username is not None
                or parsed.password is not None
                or parsed.fragment
            ):
                raise DeployConfigError(
                    "health URL must use HTTP(S), include a host, and contain "
                    "no credentials or fragment"
                )

    def _prepare_root(self) -> None:
        self.root.mkdir(parents=True, exist_ok=True)
        if self.root.is_symlink():
            raise DeployExecutionError("self-hosted deployment root became a symlink")
        releases = self.root / "releases"
        if releases.is_symlink():
            raise DeployExecutionError(
                "self-hosted releases directory must not be a symlink"
            )
        releases.mkdir(exist_ok=True)

    def _require_capacity(self, manifest: ReleaseManifest) -> None:
        free = shutil.disk_usage(self.root).free
        margin = max(256_000_000, manifest.total_bytes // 10)
        required = manifest.total_bytes + margin
        if free < required:
            raise DeployExecutionError(
                f"insufficient deployment space: need {required} bytes, have {free}"
            )

    def _install_new(
        self,
        archive: Path,
        target: Path,
        manifest: ReleaseManifest,
        release_set: ReleaseSetManifest,
        expected_sha256: str,
    ) -> None:
        target.parent.mkdir(parents=True, exist_ok=True)
        staged = target.parent / f".{target.name}-staging-{uuid.uuid4().hex}"
        staged.mkdir()
        try:
            verified = self.verifier.verify(
                archive,
                expected_sha256=expected_sha256,
                extract_to=self._public_site(staged, manifest),
            )
            if verified != manifest:
                raise DeployExecutionError("bundle changed between inspect and install")
            atomic_write_json(staged / "release-manifest.json", manifest.public_dict())
            atomic_write_json(staged / "release-set.json", release_set.public_dict())
            os.replace(staged, target)
        finally:
            if staged.exists():
                shutil.rmtree(staged)

    @staticmethod
    def _verify_installed(
        target: Path,
        manifest: ReleaseManifest,
        release_set: ReleaseSetManifest,
        *,
        expected_artifact_policy_sha256: str | None,
    ) -> None:
        SelfHostedInstaller._validate_release_set_binding(
            release_set,
            manifest,
            expected_artifact_policy_sha256=expected_artifact_policy_sha256,
        )
        site = SelfHostedInstaller._public_site(target, manifest)
        if not (site / "index.html").is_file():
            raise DeployExecutionError(f"installed release has no index: {target}")
        digest, count, total = site_tree_digest(site)
        if (
            digest != manifest.site_tree_sha256
            or count != manifest.file_count
            or total != manifest.total_bytes
        ):
            raise DeployExecutionError(
                f"installed release failed verification: {target}"
            )

    def _load_installed_manifest(self, target: Path) -> ReleaseManifest:
        path = target / "release-manifest.json"
        try:
            value = json.loads(path.read_text(encoding="utf-8"))
        except (OSError, json.JSONDecodeError) as exc:
            raise DeployExecutionError(
                f"cannot read installed release manifest: {path}"
            ) from exc
        if not isinstance(value, dict):
            raise DeployExecutionError("installed release manifest must be an object")
        manifest = ReleaseManifest.from_dict(value)
        if target != self._target(manifest.release_id, manifest.artifact):
            raise DeployExecutionError("installed release manifest/path mismatch")
        return manifest

    @staticmethod
    def _load_release_set(path: Path) -> ReleaseSetManifest:
        source = Path(path).expanduser()
        if source.is_symlink() or not source.is_file():
            raise DeployExecutionError(f"ReleaseSet is not a regular file: {source}")
        try:
            value = json.loads(source.read_text(encoding="utf-8"))
        except (OSError, json.JSONDecodeError) as exc:
            raise DeployExecutionError(f"cannot read ReleaseSet: {source}") from exc
        if not isinstance(value, dict):
            raise DeployExecutionError("ReleaseSet must be a JSON object")
        return ReleaseSetManifest.from_dict(value)

    @staticmethod
    def _validate_release_set_binding(
        release_set: ReleaseSetManifest,
        manifest: ReleaseManifest,
        *,
        expected_artifact_policy_sha256: str | None,
    ) -> None:
        record = release_set.artifact(manifest.artifact)
        expected_policy = normalize_sha256(expected_artifact_policy_sha256)
        actual_policy = normalize_sha256(release_set.artifact_policy_sha256)
        if (
            release_set.release_id != manifest.release_id
            or release_set.spec_digest != manifest.spec_digest
            or record.site_tree_sha256 != manifest.site_tree_sha256
            or record.file_count != manifest.file_count
            or record.total_bytes != manifest.total_bytes
            or (
                expected_policy is not None
                and actual_policy != expected_policy
            )
        ):
            raise DeployExecutionError(
                "ReleaseSet does not bind the self-hosted artifact"
            )

    def _target(self, release_id: str, artifact: str) -> Path:
        target = self.root / "releases" / release_id / artifact
        if target.is_symlink() or target.parent.is_symlink():
            raise DeployExecutionError(
                f"self-hosted release target must not be a symlink: {target}"
            )
        return target

    @staticmethod
    def _public_site(target: Path, manifest: ReleaseManifest) -> Path:
        parts = tuple(part for part in manifest.base_path.split("/") if part)
        return target / "public" / Path(*parts)

    @property
    def _current(self) -> Path:
        return self.root / "current"

    def _current_link_value(self) -> str | None:
        if self._current.is_symlink():
            return os.readlink(self._current)
        if self._current.exists():
            raise DeployExecutionError("self-hosted current path must be a symlink")
        return None

    def _active_target(self) -> Path | None:
        value = self._current_link_value()
        if value is None:
            return None
        return (self.root / value).resolve()

    def _active_release_id(self) -> str | None:
        target = self._active_target()
        if target is None:
            return None
        try:
            relative = target.relative_to(self.root / "releases")
        except ValueError as exc:
            raise DeployExecutionError(
                "current symlink escapes deployment releases"
            ) from exc
        return relative.parts[0] if relative.parts else None

    def _replace_current(self, target: Path) -> None:
        relative = target.relative_to(self.root).as_posix()
        temporary = self.root / f".current-{uuid.uuid4().hex}"
        temporary.symlink_to(relative, target_is_directory=True)
        try:
            if self._current.exists() and not self._current.is_symlink():
                raise DeployExecutionError("self-hosted current path must be a symlink")
            os.replace(temporary, self._current)
        finally:
            temporary.unlink(missing_ok=True)

    def _restore_current(self, previous: str | None) -> None:
        if previous is None:
            self._current.unlink(missing_ok=True)
            return
        temporary = self.root / f".current-rollback-{uuid.uuid4().hex}"
        temporary.symlink_to(previous, target_is_directory=True)
        try:
            os.replace(temporary, self._current)
        finally:
            temporary.unlink(missing_ok=True)

    def _probe(
        self,
        manifest: ReleaseManifest,
        *,
        health_url: str | None,
        filesystem_health_only: bool,
        attempts: int,
        interval: float,
    ) -> None:
        if filesystem_health_only:
            spec = (
                self._public_site(self._current, manifest)
                / "release-spec.json"
            )
            try:
                value = json.loads(spec.read_text(encoding="utf-8"))
            except (OSError, json.JSONDecodeError) as exc:
                raise DeployExecutionError("active release has no valid ReleaseSpec") from exc
            self._validate_health_payload(value, manifest)
            return
        assert health_url is not None
        last_error: Exception | None = None
        for attempt in range(attempts):
            try:
                with urlopen(health_url, timeout=max(1.0, interval)) as response:
                    if not 200 <= response.status < 400:
                        raise DeployExecutionError(
                            f"health endpoint returned HTTP {response.status}"
                        )
                    value = json.loads(response.read().decode("utf-8"))
                self._validate_health_payload(value, manifest)
                return
            except (
                OSError,
                URLError,
                UnicodeError,
                json.JSONDecodeError,
                DeployExecutionError,
            ) as exc:
                last_error = exc
                if attempt + 1 < attempts:
                    time.sleep(interval)
        raise DeployExecutionError(f"self-hosted health check failed: {last_error}")

    @staticmethod
    def _validate_health_payload(value: object, manifest: ReleaseManifest) -> None:
        if not isinstance(value, dict):
            raise DeployExecutionError(
                "health endpoint did not return a JSON object"
            )
        if (
            value.get("release_id") != manifest.release_id
            or value.get("spec_digest") != manifest.spec_digest
        ):
            raise DeployExecutionError("health endpoint reports another release")

    @contextmanager
    def _locked(self) -> Iterator[None]:
        lock = self.root / "deploy.lock"
        with lock.open("a+", encoding="utf-8") as handle:
            fcntl.flock(handle.fileno(), fcntl.LOCK_EX)
            try:
                yield
            finally:
                fcntl.flock(handle.fileno(), fcntl.LOCK_UN)


__all__ = ["SelfHostedDeployment", "SelfHostedInstaller"]
