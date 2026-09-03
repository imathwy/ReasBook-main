"""Deterministic release bundle creation and safe verification."""

from __future__ import annotations

from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path, PurePosixPath
import shutil
import tempfile
import uuid

from reasbook_sdk_common import (
    Command,
    CommandExecutionError,
    CommandRunner,
    atomic_write_json,
    atomic_write_text,
)

from ..errors import DeployConfigError, DeployExecutionError
from .models import ReleaseArtifactPolicy, ReleaseSpec
from .results import (
    BundleInfo,
    ReleaseBuildReport,
    ReleaseManifest,
)
from .store import ReleaseLayout, ReleaseStore


def sha256_file(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        while chunk := handle.read(1024 * 1024):
            digest.update(chunk)
    return digest.hexdigest()


def site_tree_digest(root: Path) -> tuple[str, int, int]:
    """Hash paths, sizes, and contents in deterministic order."""

    if not root.is_dir() or root.is_symlink():
        raise DeployExecutionError(f"site root is not a directory: {root}")
    digest = hashlib.sha256()
    file_count = 0
    total_bytes = 0
    for path in sorted(root.rglob("*"), key=lambda item: item.as_posix()):
        if path.is_symlink():
            raise DeployExecutionError(f"site contains a symlink: {path}")
        if path.is_dir():
            continue
        if not path.is_file():
            raise DeployExecutionError(f"site contains a special file: {path}")
        relative = path.relative_to(root).as_posix()
        size = path.stat().st_size
        content_digest = sha256_file(path)
        digest.update(relative.encode("utf-8"))
        digest.update(b"\0")
        digest.update(f"{size}:{content_digest}".encode("ascii"))
        digest.update(b"\n")
        file_count += 1
        total_bytes += size
    if file_count == 0:
        raise DeployExecutionError("site tree is empty")
    return f"sha256:{digest.hexdigest()}", file_count, total_bytes


class ReleaseBundler:
    """Create a reproducible tar.zst and its external checksum record."""

    def __init__(
        self,
        layout: ReleaseLayout,
        store: ReleaseStore,
        *,
        generated_at: datetime | None = None,
    ) -> None:
        self.layout = layout
        self.store = store
        self.generated_at = generated_at

    def package(
        self,
        spec: ReleaseSpec,
        report: ReleaseBuildReport,
        *,
        policy: ReleaseArtifactPolicy | None = None,
    ) -> BundleInfo:
        effective_policy = policy or ReleaseArtifactPolicy(
            name="full",
            history_mode="full",
            dependency_docs="stubs",
            max_site_files=spec.policy.max_site_files,
            max_site_bytes=100_000_000_000,
            max_bundle_bytes=spec.policy.max_bundle_bytes,
        )
        if effective_policy.name != "full":
            raise DeployConfigError("full release packaging requires the full policy")
        return self._package_site(
            spec,
            report,
            site=self.layout.site,
            package_root=self.layout.root,
            bundle_path=self.layout.bundle,
            manifest_path=self.layout.manifest,
            checksums_path=self.layout.checksums,
            policy=effective_policy,
        )

    def package_pages(
        self,
        spec: ReleaseSpec,
        report: ReleaseBuildReport,
        *,
        policy: ReleaseArtifactPolicy,
    ) -> BundleInfo:
        if policy.name != "pages":
            raise DeployConfigError("Pages packaging requires the pages policy")
        return self._package_site(
            spec,
            report,
            site=self.layout.pages_site,
            package_root=self.layout.pages_root,
            bundle_path=self.layout.pages_bundle,
            manifest_path=self.layout.pages_manifest,
            checksums_path=self.layout.pages_checksums,
            policy=policy,
        )

    def _package_site(
        self,
        spec: ReleaseSpec,
        report: ReleaseBuildReport,
        *,
        site: Path,
        package_root: Path,
        bundle_path: Path,
        manifest_path: Path,
        checksums_path: Path,
        policy: ReleaseArtifactPolicy,
    ) -> BundleInfo:
        if report.status == "failed":
            raise DeployExecutionError("cannot package a failed release")
        if not (site / "index.html").is_file():
            raise DeployExecutionError("release site has no index.html")
        tree_digest, file_count, total_bytes = site_tree_digest(site)
        if file_count > policy.max_site_files:
            raise DeployExecutionError(
                f"site has {file_count} files; budget is "
                f"{policy.max_site_files} for {policy.name}"
            )
        if total_bytes > policy.max_site_bytes:
            raise DeployExecutionError(
                f"site is {total_bytes} bytes; budget is "
                f"{policy.max_site_bytes} for {policy.name}"
            )
        now = self.generated_at or datetime.fromisoformat(
            spec.resolved_at.replace("Z", "+00:00")
        )
        by_branch = {branch.branch: branch for branch in report.branches}
        manifest = ReleaseManifest(
            release_id=spec.release_id,
            spec_digest=spec.spec_digest,
            status=report.status,
            base_path=spec.base_path,
            generated_at=now.astimezone(timezone.utc)
            .isoformat(timespec="seconds")
            .replace("+00:00", "Z"),
            site_tree_sha256=tree_digest,
            file_count=file_count,
            total_bytes=total_bytes,
            projects=tuple(
                {
                    **project.public_dict(),
                    "status": by_branch[project.branch].status,
                }
                for project in spec.projects
            ),
            branches=tuple(
                {
                    "branch": branch.branch,
                    "commit": branch.commit,
                    "status": branch.status,
                    "stages": [
                        {
                            "name": stage.name,
                            "status": stage.status,
                        }
                        for stage in branch.stages
                    ],
                }
                for branch in report.branches
            ),
            artifact=policy.name,
        )
        package_root.mkdir(parents=True, exist_ok=True)
        atomic_write_json(manifest_path, manifest.public_dict())
        self._create_archive(package_root, bundle_path)
        bundle_size = bundle_path.stat().st_size
        if bundle_size > policy.max_bundle_bytes:
            raise DeployExecutionError(
                f"bundle is {bundle_size} bytes; budget is "
                f"{policy.max_bundle_bytes} for {policy.name}"
            )
        bundle_digest = sha256_file(bundle_path)
        atomic_write_text(
            checksums_path,
            f"{bundle_digest}  {bundle_path.name}\n",
        )
        info = BundleInfo(
            spec.release_id,
            str(bundle_path),
            str(manifest_path),
            str(checksums_path),
            f"sha256:{bundle_digest}",
            artifact=policy.name,
        )
        if policy.name == "full":
            self.store.write_manifest(manifest)
            self.store.write_bundle_info(info)
        else:
            self.store.write_pages_bundle_info(info)
        return info

    def _create_archive(self, package_root: Path, bundle_path: Path) -> None:
        temporary = package_root / f".bundle-{uuid.uuid4().hex}.tar.zst"
        command = Command(
            (
                "tar",
                "--sort=name",
                "--mtime=@0",
                "--owner=0",
                "--group=0",
                "--numeric-owner",
                "--pax-option=delete=atime,delete=ctime",
                "--zstd",
                "-cf",
                str(temporary),
                "-C",
                str(package_root),
                "site",
                "release-manifest.json",
            ),
            cwd=package_root,
            # Keep the worker count fixed so repeated bundles remain
            # reproducible while large documentation trees use more than one
            # CPU during compression.
            env={"ZSTD_NBTHREADS": "8"},
            timeout=1800.0,
        )
        try:
            result = CommandRunner().run(command)
        except CommandExecutionError as exc:
            temporary.unlink(missing_ok=True)
            raise DeployExecutionError(f"cannot start release archiver: {exc}") from exc
        if result.returncode != 0:
            temporary.unlink(missing_ok=True)
            detail = (result.stderr or result.stdout).strip()
            raise DeployExecutionError(
                "could not create release bundle" + (f": {detail}" if detail else "")
            )
        try:
            os.replace(temporary, bundle_path)
        except OSError:
            temporary.unlink(missing_ok=True)
            raise


class BundleVerifier:
    """Verify checksums, archive paths, manifest, and extracted site digest."""

    def inspect(
        self,
        bundle: Path,
        *,
        expected_sha256: str | None = None,
    ) -> ReleaseManifest:
        """Validate archive metadata without materializing the complete site."""

        archive = Path(bundle).expanduser().resolve()
        if not archive.is_file() or archive.is_symlink():
            raise DeployConfigError(f"bundle does not exist: {archive}")
        actual = sha256_file(archive)
        if expected_sha256:
            normalized = expected_sha256.removeprefix("sha256:")
            if normalized != actual:
                raise DeployExecutionError(
                    f"bundle checksum mismatch: expected {normalized}, got {actual}"
                )
        names = self._list_archive(archive)
        self._validate_members(names)
        manifest = ReleaseManifest.from_dict(
            self._read_archive_json(archive, "release-manifest.json")
        )
        spec = ReleaseSpec.from_dict(
            self._read_archive_json(archive, "site/release-spec.json")
        )
        if (
            spec.release_id != manifest.release_id
            or spec.spec_digest != manifest.spec_digest
            or spec.base_path != manifest.base_path
        ):
            raise DeployExecutionError(
                "bundle manifest does not match its ReleaseSpec"
            )
        return manifest

    def verify(
        self,
        bundle: Path,
        *,
        expected_sha256: str | None = None,
        extract_to: Path | None = None,
    ) -> ReleaseManifest:
        archive = Path(bundle).expanduser().resolve()
        inspected = self.inspect(archive, expected_sha256=expected_sha256)
        target = self._extraction_target(extract_to)
        temp_parent = archive.parent
        if target is not None:
            target.parent.mkdir(parents=True, exist_ok=True)
            temp_parent = target.parent
        with tempfile.TemporaryDirectory(
            prefix=".reasbook-bundle-",
            dir=str(temp_parent),
        ) as temp:
            extracted = Path(temp)
            self._extract(archive, extracted)
            self._validate_extracted_tree(extracted)
            manifest = self._read_manifest(extracted / "release-manifest.json")
            spec = self._read_spec(extracted / "site" / "release-spec.json")
            if (
                manifest != inspected
                or spec.release_id != manifest.release_id
                or spec.spec_digest != manifest.spec_digest
                or spec.base_path != manifest.base_path
            ):
                raise DeployExecutionError(
                    "bundle manifest does not match its ReleaseSpec"
                )
            digest, count, total = site_tree_digest(extracted / "site")
            if (
                digest != manifest.site_tree_sha256
                or count != manifest.file_count
                or total != manifest.total_bytes
            ):
                raise DeployExecutionError(
                    "bundle site tree does not match release manifest"
                )
            if target is not None:
                self._publish_extracted(extracted / "site", target)
            return manifest

    @staticmethod
    def _extraction_target(value: Path | None) -> Path | None:
        if value is None:
            return None
        target = Path(value).expanduser().resolve(strict=False)
        if target in {Path("/"), Path.home().resolve()}:
            raise DeployConfigError(
                f"refusing to replace broad extraction target: {target}"
            )
        return target

    @staticmethod
    def _read_archive_json(bundle: Path, member: str) -> dict:
        try:
            result = CommandRunner().run(
                Command(
                    ("tar", "--zstd", "-xOf", str(bundle), member),
                    cwd=bundle.parent,
                    timeout=300.0,
                )
            )
        except CommandExecutionError as exc:
            raise DeployExecutionError(
                f"cannot read {member} from release bundle: {exc}"
            ) from exc
        if result.returncode != 0:
            raise DeployExecutionError(f"cannot read {member} from release bundle")
        try:
            value = json.loads(result.stdout)
        except json.JSONDecodeError as exc:
            raise DeployExecutionError(
                f"release bundle member is not valid JSON: {member}"
            ) from exc
        if not isinstance(value, dict):
            raise DeployExecutionError(
                f"release bundle member must be an object: {member}"
            )
        return value

    @staticmethod
    def _list_archive(bundle: Path) -> tuple[str, ...]:
        runner = CommandRunner()
        try:
            result = runner.run(
                Command(
                    ("tar", "--zstd", "-tf", str(bundle)),
                    cwd=bundle.parent,
                    timeout=300.0,
                )
            )
        except CommandExecutionError as exc:
            raise DeployExecutionError(f"cannot inspect release bundle: {exc}") from exc
        if result.returncode != 0:
            raise DeployExecutionError("cannot list release bundle")
        try:
            verbose = runner.run(
                Command(
                    ("tar", "--zstd", "-tvf", str(bundle)),
                    cwd=bundle.parent,
                    timeout=300.0,
                )
            )
        except CommandExecutionError as exc:
            raise DeployExecutionError(f"cannot inspect release bundle: {exc}") from exc
        if verbose.returncode != 0:
            raise DeployExecutionError("cannot inspect release bundle types")
        unsupported = [
            line
            for line in verbose.stdout.splitlines()
            if line and line[0] not in {"-", "d"}
        ]
        if unsupported:
            raise DeployExecutionError(
                "bundle contains links or special archive members"
            )
        return tuple(line for line in result.stdout.splitlines() if line)

    @staticmethod
    def _validate_members(names: tuple[str, ...]) -> None:
        if "release-manifest.json" not in names:
            raise DeployExecutionError("bundle has no release-manifest.json")
        if not any(name.startswith("site/") for name in names):
            raise DeployExecutionError("bundle has no site tree")
        for name in names:
            path = PurePosixPath(name)
            if (
                path.is_absolute()
                or any(part in {"", ".", ".."} for part in path.parts)
                or not (
                    name == "release-manifest.json"
                    or name == "site"
                    or name.startswith("site/")
                )
            ):
                raise DeployExecutionError(f"unsafe bundle member: {name!r}")

    @staticmethod
    def _extract(bundle: Path, destination: Path) -> None:
        try:
            result = CommandRunner().run(
                Command(
                    (
                        "tar",
                        "--zstd",
                        "--extract",
                        "--file",
                        str(bundle),
                        "--directory",
                        str(destination),
                        "--no-same-owner",
                        "--no-same-permissions",
                    ),
                    cwd=destination,
                    timeout=600.0,
                )
            )
        except CommandExecutionError as exc:
            raise DeployExecutionError(f"cannot extract release bundle: {exc}") from exc
        if result.returncode != 0:
            raise DeployExecutionError("cannot extract release bundle")

    @staticmethod
    def _validate_extracted_tree(root: Path) -> None:
        for path in root.rglob("*"):
            if path.is_symlink():
                raise DeployExecutionError(
                    f"bundle contains a symlink: {path.relative_to(root)}"
                )
            if not path.is_dir() and not path.is_file():
                raise DeployExecutionError(
                    f"bundle contains a special file: {path.relative_to(root)}"
                )

    @staticmethod
    def _read_manifest(path: Path) -> ReleaseManifest:
        try:
            value = json.loads(path.read_text(encoding="utf-8"))
        except (OSError, json.JSONDecodeError) as exc:
            raise DeployExecutionError(f"invalid bundle manifest: {exc}") from exc
        if not isinstance(value, dict):
            raise DeployExecutionError("bundle manifest must be an object")
        return ReleaseManifest.from_dict(value)

    @staticmethod
    def _read_spec(path: Path) -> ReleaseSpec:
        try:
            value = json.loads(path.read_text(encoding="utf-8"))
        except (OSError, json.JSONDecodeError) as exc:
            raise DeployExecutionError(f"invalid bundled ReleaseSpec: {exc}") from exc
        if not isinstance(value, dict):
            raise DeployExecutionError("bundled ReleaseSpec must be an object")
        return ReleaseSpec.from_dict(value)

    @staticmethod
    def _publish_extracted(source: Path, destination: Path) -> None:
        target = BundleVerifier._extraction_target(destination)
        assert target is not None
        target.parent.mkdir(parents=True, exist_ok=True)
        backup = target.parent / f".{target.name}-backup-{uuid.uuid4().hex}"
        had_target = target.exists() or target.is_symlink()
        if had_target:
            os.replace(target, backup)
        try:
            os.replace(source, target)
        except OSError:
            if had_target and not (target.exists() or target.is_symlink()):
                os.replace(backup, target)
            raise
        if had_target:
            if backup.is_dir() and not backup.is_symlink():
                shutil.rmtree(backup)
            else:
                backup.unlink(missing_ok=True)


__all__ = [
    "BundleVerifier",
    "ReleaseBundler",
    "sha256_file",
    "site_tree_digest",
]
