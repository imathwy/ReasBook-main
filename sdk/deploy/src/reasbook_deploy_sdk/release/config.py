"""Load and validate human-maintained release configuration."""

from __future__ import annotations

from pathlib import Path
from typing import Any, Mapping

from reasbook_sdk_common import ensure_within

from ..errors import DeployConfigError
from .models import (
    CanonicalProjects,
    DeploymentProfile,
    GitHubPublishProfile,
    ReleaseArtifactPolicy,
    RegistryBranch,
    ReleasePolicy,
    ToolchainRegistry,
    default_artifact_policies,
)


def _load_yaml(path: Path) -> dict[str, Any]:
    try:
        import yaml
    except ModuleNotFoundError as exc:
        raise DeployConfigError(
            "release YAML support requires PyYAML; install the deploy SDK"
        ) from exc
    try:
        value = yaml.safe_load(path.read_text(encoding="utf-8"))
    except (OSError, UnicodeError, yaml.YAMLError) as exc:
        raise DeployConfigError(f"cannot read YAML {path}: {exc}") from exc
    if not isinstance(value, Mapping):
        raise DeployConfigError(f"YAML root must be an object: {path}")
    return dict(value)


def _mapping(value: object, *, field: str) -> dict[str, Any]:
    if not isinstance(value, Mapping):
        raise DeployConfigError(f"{field} must be an object")
    return {str(key): item for key, item in value.items()}


def _expect_keys(
    value: Mapping[str, Any],
    allowed: set[str],
    *,
    field: str,
) -> None:
    unknown = sorted(set(value) - allowed)
    if unknown:
        raise DeployConfigError(f"{field} has unknown fields: {', '.join(unknown)}")


def _schema_version(value: Mapping[str, Any], path: Path) -> None:
    if value.get("schema_version") != 1:
        raise DeployConfigError(f"{path} must use schema_version: 1")


def _boolean(value: object, *, default: bool, field: str) -> bool:
    if value is None:
        return default
    if not isinstance(value, bool):
        raise DeployConfigError(f"{field} must be true or false")
    return value


def _positive_integer(value: object, *, default: int, field: str) -> int:
    if value is None:
        return default
    if isinstance(value, bool) or not isinstance(value, int) or value < 1:
        raise DeployConfigError(f"{field} must be a positive integer")
    return value


def _repo_file(repo_root: Path, value: object, *, field: str) -> Path:
    path = Path(str(value)).expanduser()
    if not path.is_absolute():
        path = repo_root / path
    try:
        path = ensure_within(path.resolve(strict=False), repo_root, field=field)
    except ValueError as exc:
        raise DeployConfigError(str(exc)) from exc
    if not path.is_file():
        raise DeployConfigError(f"{field} does not exist: {path}")
    return path


def load_profile(path: str | Path, *, repo_root: str | Path) -> DeploymentProfile:
    root = Path(repo_root).expanduser().resolve()
    profile_path = Path(path).expanduser()
    if not profile_path.is_absolute():
        profile_path = root / profile_path
    profile_path = profile_path.resolve()
    value = _load_yaml(profile_path)
    _schema_version(value, profile_path)
    _expect_keys(
        value,
        {
            "schema_version",
            "name",
            "registry",
            "canonical_projects",
            "selection",
            "site",
            "policy",
            "artifacts",
            "publish",
        },
        field="profile",
    )

    selection_value = value.get("selection", {"mode": "all_active"})
    if isinstance(selection_value, str):
        selection = {"mode": selection_value}
    else:
        selection = _mapping(selection_value, field="selection")
    _expect_keys(selection, {"mode", "exclude"}, field="selection")
    if selection.get("mode", "all_active") != "all_active":
        raise DeployConfigError("selection.mode currently supports only all_active")
    raw_exclude = selection.get("exclude", [])
    if not isinstance(raw_exclude, list) or not all(
        isinstance(item, str) for item in raw_exclude
    ):
        raise DeployConfigError("selection.exclude must be an array of project keys")

    site = _mapping(value.get("site"), field="site")
    _expect_keys(
        site,
        {"base_path", "include_historical_versions"},
        field="site",
    )
    policy_value = _mapping(value.get("policy", {}), field="policy")
    _expect_keys(
        policy_value,
        {
            "allow_partial",
            "require_lean",
            "require_docs",
            "require_verso",
            "theorem_graph",
            "max_site_files",
            "max_bundle_bytes",
        },
        field="policy",
    )
    publish_value = _mapping(value.get("publish"), field="publish")
    _expect_keys(
        publish_value,
        {"adapter", "repository", "release_tag_prefix", "workflow"},
        field="publish",
    )
    if publish_value.get("adapter") != "github_pages":
        raise DeployConfigError("publish.adapter currently supports only github_pages")

    defaults = {item.name: item for item in default_artifact_policies()}
    artifacts_value = value.get("artifacts")
    if artifacts_value is None:
        artifacts = tuple(defaults.values())
    else:
        artifact_mapping = _mapping(artifacts_value, field="artifacts")
        _expect_keys(artifact_mapping, {"full", "pages"}, field="artifacts")
        if set(artifact_mapping) != {"full", "pages"}:
            raise DeployConfigError("artifacts must define both full and pages")
        parsed_artifacts: list[ReleaseArtifactPolicy] = []
        for name in ("full", "pages"):
            item = _mapping(artifact_mapping[name], field=f"artifacts.{name}")
            _expect_keys(
                item,
                {
                    "history_mode",
                    "dependency_docs",
                    "max_site_files",
                    "max_site_bytes",
                    "max_bundle_bytes",
                },
                field=f"artifacts.{name}",
            )
            default = defaults[name]
            parsed_artifacts.append(
                ReleaseArtifactPolicy(
                    name=name,
                    history_mode=str(
                        item.get("history_mode", default.history_mode)
                    ),
                    dependency_docs=str(
                        item.get("dependency_docs", default.dependency_docs)
                    ),
                    max_site_files=_positive_integer(
                        item.get("max_site_files"),
                        default=default.max_site_files,
                        field=f"artifacts.{name}.max_site_files",
                    ),
                    max_site_bytes=_positive_integer(
                        item.get("max_site_bytes"),
                        default=default.max_site_bytes,
                        field=f"artifacts.{name}.max_site_bytes",
                    ),
                    max_bundle_bytes=_positive_integer(
                        item.get("max_bundle_bytes"),
                        default=default.max_bundle_bytes,
                        field=f"artifacts.{name}.max_bundle_bytes",
                    ),
                )
            )
        artifacts = tuple(parsed_artifacts)

    return DeploymentProfile(
        name=str(value.get("name", "")),
        registry=_repo_file(root, value.get("registry"), field="registry"),
        canonical_projects=_repo_file(
            root,
            value.get("canonical_projects"),
            field="canonical_projects",
        ),
        base_path=str(site.get("base_path", "/")),
        include_historical_versions=_boolean(
            site.get("include_historical_versions"),
            default=True,
            field="site.include_historical_versions",
        ),
        policy=ReleasePolicy(
            allow_partial=_boolean(
                policy_value.get("allow_partial"),
                default=False,
                field="policy.allow_partial",
            ),
            require_lean=_boolean(
                policy_value.get("require_lean"),
                default=True,
                field="policy.require_lean",
            ),
            require_docs=_boolean(
                policy_value.get("require_docs"),
                default=True,
                field="policy.require_docs",
            ),
            require_verso=_boolean(
                policy_value.get("require_verso"),
                default=True,
                field="policy.require_verso",
            ),
            theorem_graph=str(policy_value.get("theorem_graph", "compiled_or_source")),
            max_site_files=_positive_integer(
                policy_value.get("max_site_files"),
                default=100000,
                field="policy.max_site_files",
            ),
            max_bundle_bytes=_positive_integer(
                policy_value.get("max_bundle_bytes"),
                default=1900000000,
                field="policy.max_bundle_bytes",
            ),
        ),
        publish=GitHubPublishProfile(
            repository=str(publish_value.get("repository", "")),
            release_tag_prefix=str(
                publish_value.get("release_tag_prefix", "reasbook-site")
            ),
            workflow=str(publish_value.get("workflow", "publish_release_pages.yml")),
        ),
        exclude=tuple(sorted(set(raw_exclude))),
        artifacts=artifacts,
    )


def load_registry(path: str | Path) -> ToolchainRegistry:
    source = Path(path).expanduser().resolve()
    value = _load_yaml(source)
    _schema_version(value, source)
    _expect_keys(value, {"schema_version", "branches"}, field="toolchain registry")
    raw_branches = value.get("branches")
    if not isinstance(raw_branches, list):
        raise DeployConfigError("toolchain registry branches must be an array")
    branches: list[RegistryBranch] = []
    for index, item in enumerate(raw_branches):
        record = _mapping(item, field=f"branches[{index}]")
        _expect_keys(
            record,
            {"version", "branch", "status", "initialization"},
            field=f"branches[{index}]",
        )
        branches.append(
            RegistryBranch(
                version=str(record.get("version", "")),
                branch=str(record.get("branch", "")),
                status=str(record.get("status", "active")),
            )
        )
    if len({branch.branch for branch in branches}) != len(branches):
        raise DeployConfigError("toolchain registry contains duplicate branches")
    return ToolchainRegistry(tuple(branches))


def load_canonical_projects(path: str | Path) -> CanonicalProjects:
    source = Path(path).expanduser().resolve()
    value = _load_yaml(source)
    _schema_version(value, source)
    _expect_keys(value, {"schema_version", "books", "papers"}, field="canonical map")
    entries: list[tuple[str, str]] = []
    for kind in ("books", "papers"):
        projects = _mapping(value.get(kind, {}), field=f"canonical.{kind}")
        for project, branch in projects.items():
            entries.append((f"{kind}/{project}", str(branch)))
    return CanonicalProjects(tuple(sorted(entries)))


def dump_profile_snapshot(profile: DeploymentProfile) -> str:
    """Serialize a self-contained profile that references sibling snapshots."""

    try:
        import yaml
    except ModuleNotFoundError as exc:
        raise DeployConfigError(
            "release YAML support requires PyYAML; install the deploy SDK"
        ) from exc
    value = {
        "schema_version": 1,
        "name": profile.name,
        "registry": "toolchains.yml",
        "canonical_projects": "canonical-projects.yml",
        "selection": {
            "mode": "all_active",
            "exclude": list(profile.exclude),
        },
        "site": {
            "base_path": profile.base_path,
            "include_historical_versions": (profile.include_historical_versions),
        },
        "policy": profile.policy.public_dict(),
        "artifacts": {
            artifact.name: artifact.public_dict()
            for artifact in profile.artifacts
        },
        "publish": profile.publish.public_dict(),
    }
    return yaml.safe_dump(value, sort_keys=False, allow_unicode=False)


__all__ = [
    "load_canonical_projects",
    "dump_profile_snapshot",
    "load_profile",
    "load_registry",
]
