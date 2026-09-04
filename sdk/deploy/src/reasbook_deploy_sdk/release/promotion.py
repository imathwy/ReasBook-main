"""Fail-closed promotion gate for persisted local acceptance evidence."""

from __future__ import annotations

import json
from pathlib import Path
from typing import Any, Mapping

from ..errors import DeployExecutionError
from .bundle import normalize_sha256, sha256_file
from .models import ReleaseSpec
from .store import ReleaseLayout, ReleaseStore


def _object(value: object, *, label: str) -> Mapping[str, Any]:
    if not isinstance(value, dict):
        raise DeployExecutionError(f"acceptance evidence has invalid {label}")
    return value


def _read_evidence(path: Path) -> Mapping[str, Any]:
    if path.is_symlink() or not path.is_file():
        raise DeployExecutionError(
            "required release acceptance evidence is missing; run `release "
            "validate RELEASE_ID --browser-mode required`"
        )
    try:
        value = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, UnicodeError, json.JSONDecodeError) as exc:
        raise DeployExecutionError("release acceptance evidence is invalid") from exc
    return _object(value, label="root")


def require_release_acceptance(
    layout: ReleaseLayout,
    spec: ReleaseSpec,
    *,
    expected_artifact_policy_sha256: str,
) -> Mapping[str, Any]:
    """Bind a successful browser gate to the package being promoted now."""

    validation_root = layout.cache_root / "validation"
    release_root = validation_root / spec.release_id
    if validation_root.is_symlink() or release_root.is_symlink():
        raise DeployExecutionError("release acceptance evidence path is unsafe")
    evidence = _read_evidence(release_root / "latest.json")

    normalized_policy = normalize_sha256(expected_artifact_policy_sha256)
    assert normalized_policy is not None
    expected_policy = f"sha256:{normalized_policy}"
    if (
        evidence.get("status") != "success"
        or evidence.get("release_id") != spec.release_id
        or evidence.get("spec_digest") != spec.spec_digest
        or evidence.get("artifact_policy_sha256") != expected_policy
    ):
        raise DeployExecutionError(
            "release acceptance evidence does not match the current ReleaseSpec"
        )

    metadata = _object(evidence.get("metadata"), label="metadata")
    metadata_artifacts = _object(
        metadata.get("artifacts"),
        label="metadata artifacts",
    )
    expected_release_set_path = layout.release_set.resolve(strict=False)
    if (
        set(metadata) != {"release_set", "release_set_sha256", "artifacts"}
        or metadata.get("release_set") != str(expected_release_set_path)
        or set(metadata_artifacts) != {"full", "pages"}
        or layout.release_set.is_symlink()
        or not layout.release_set.is_file()
        or metadata.get("release_set_sha256")
        != "sha256:" + sha256_file(layout.release_set)
    ):
        raise DeployExecutionError(
            "accepted ReleaseSet metadata changed before promotion"
        )

    store = ReleaseStore(layout)
    release_set = store.load_release_set()
    bundles = {
        "full": store.load_bundle_info(),
        "pages": store.load_pages_bundle_info(),
    }
    expected_paths = {
        "full": (layout.bundle, layout.manifest, layout.checksums),
        "pages": (
            layout.pages_bundle,
            layout.pages_manifest,
            layout.pages_checksums,
        ),
    }
    if (
        release_set.release_id != spec.release_id
        or release_set.spec_digest != spec.spec_digest
        or release_set.artifact_policy_sha256 != expected_policy
    ):
        raise DeployExecutionError(
            "current ReleaseSet does not match the accepted release"
        )

    artifacts = _object(evidence.get("artifacts"), label="artifacts")
    if set(artifacts) != {"full", "pages"}:
        raise DeployExecutionError(
            "acceptance evidence must contain exactly full and pages artifacts"
        )
    for name, bundle in bundles.items():
        accepted = _object(artifacts[name], label=f"{name} artifact")
        record = release_set.artifact(name)
        bundle_path = Path(bundle.bundle).expanduser()
        metadata_paths = tuple(
            Path(value).expanduser()
            for value in (bundle.manifest, bundle.checksums)
        )
        accepted_metadata = _object(
            metadata_artifacts[name],
            label=f"{name} metadata",
        )
        expected_manifest = metadata_paths[0].resolve(strict=False)
        expected_checksums = metadata_paths[1].resolve(strict=False)
        if (
            bundle_path.is_symlink()
            or not bundle_path.is_file()
            or any(
                path.is_symlink() or not path.is_file()
                for path in metadata_paths
            )
        ):
            raise DeployExecutionError(
                f"{name} package contains a missing or unsafe release file"
            )
        if (
            set(accepted_metadata)
            != {
                "manifest",
                "manifest_sha256",
                "checksums",
                "checksums_sha256",
            }
            or accepted_metadata.get("manifest") != str(expected_manifest)
            or accepted_metadata.get("checksums") != str(expected_checksums)
            or accepted_metadata.get("manifest_sha256")
            != "sha256:" + sha256_file(metadata_paths[0])
            or accepted_metadata.get("checksums_sha256")
            != "sha256:" + sha256_file(metadata_paths[1])
        ):
            raise DeployExecutionError(
                f"{name} metadata changed after release acceptance"
            )
        expected_bundle_sha256 = normalize_sha256(bundle.bundle_sha256)
        assert expected_bundle_sha256 is not None
        if sha256_file(bundle_path) != expected_bundle_sha256:
            raise DeployExecutionError(
                f"{name} bundle changed after release acceptance"
            )
        bundle_paths = tuple(
            Path(value).expanduser().resolve(strict=False)
            for value in (bundle.bundle, bundle.manifest, bundle.checksums)
        )
        if (
            bundle.artifact != name
            or bundle.release_id != spec.release_id
            or bundle_paths
            != tuple(path.resolve(strict=False) for path in expected_paths[name])
            or bundle.release_set is None
            or Path(bundle.release_set).expanduser().resolve(strict=False)
            != layout.release_set.resolve(strict=False)
            or layout.release_set.is_symlink()
            or not layout.release_set.is_file()
            or record.bundle != Path(bundle.bundle).name
            or record.bundle_sha256 != bundle.bundle_sha256
            or accepted.get("bundle") != bundle.bundle
            or accepted.get("bundle_sha256") != bundle.bundle_sha256
            or accepted.get("site_tree_sha256") != record.site_tree_sha256
            or accepted.get("file_count") != record.file_count
            or isinstance(accepted.get("file_count"), bool)
            or accepted.get("total_bytes") != record.total_bytes
            or isinstance(accepted.get("total_bytes"), bool)
        ):
            raise DeployExecutionError(
                f"{name} acceptance evidence does not match the current package"
            )
        http = _object(accepted.get("http"), label=f"{name} HTTP result")
        browser = _object(
            accepted.get("browser"),
            label=f"{name} browser result",
        )
        if http.get("status") != "passed" or browser.get("status") != "passed":
            raise DeployExecutionError(
                f"{name} acceptance did not pass HTTP and required browser checks"
            )

    self_hosted = _object(evidence.get("self_hosted"), label="self-hosted result")
    if (
        self_hosted.get("status") != "success"
        or self_hosted.get("release_id") != spec.release_id
        or self_hosted.get("filesystem_health") != "passed"
    ):
        raise DeployExecutionError(
            "self-hosted acceptance did not pass the production installer check"
        )
    return evidence


__all__ = ["require_release_acceptance"]
