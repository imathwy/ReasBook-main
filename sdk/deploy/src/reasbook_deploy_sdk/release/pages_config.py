"""Fail-closed GitHub Pages repository and environment configuration."""

from __future__ import annotations

from dataclasses import dataclass
import json
from pathlib import Path
import re
from typing import Any

from ..errors import DeployExecutionError
from .github_client import GitHubRepositoryClient


@dataclass(frozen=True)
class GitHubPagesConfiguration:
    """Result of configuring the repository-owned Pages deployment boundary."""

    repository: str
    default_branch: str
    workflow: str
    status: str
    actions: tuple[str, ...]

    def __post_init__(self) -> None:
        if self.status not in {"planned", "configured", "ready"}:
            raise DeployExecutionError(
                f"invalid GitHub Pages configuration status: {self.status}"
            )

    def public_dict(self) -> dict[str, Any]:
        return {
            "repository": self.repository,
            "default_branch": self.default_branch,
            "workflow": self.workflow,
            "environment": "github-pages",
            "status": self.status,
            "actions": list(self.actions),
        }


@dataclass(frozen=True)
class _PolicyRemoval:
    policy_id: int
    expected_name: str
    expected_type: str


class GitHubPagesConfigurator(GitHubRepositoryClient):
    """Create missing Pages settings, while refusing to rewrite incompatible ones."""

    _ENVIRONMENT = "github-pages"

    def configure(
        self,
        *,
        dry_run: bool = False,
        remove_policy_id: int | None = None,
        expected_policy_name: str | None = None,
        expected_policy_type: str | None = None,
    ) -> GitHubPagesConfiguration:
        removal = self._policy_removal(
            remove_policy_id,
            expected_policy_name,
            expected_policy_type,
        )
        default_branch = self._default_branch()
        trusted_sha = self._trusted_target(default_branch)
        self._verify_workflow(trusted_sha)

        immutable_releases_enabled = self._immutable_releases_enabled()
        pages_endpoint = f"repos/{self.profile.repository}/pages"
        environment_endpoint = (
            f"repos/{self.profile.repository}/environments/{self._ENVIRONMENT}"
        )
        policy_endpoint = f"{environment_endpoint}/deployment-branch-policies"

        pages = self._get_optional(pages_endpoint, label="Pages site")
        environment = self._get_optional(
            environment_endpoint,
            label="github-pages environment",
        )
        policies = None
        if environment is not None:
            policies = self._get_required(
                f"{policy_endpoint}?per_page=100",
                label="github-pages deployment policies",
            )

        self._validate_pages(pages)
        if removal is None:
            self._validate_environment(
                environment,
                policies,
                default_branch,
                allow_missing_default_policy=True,
            )
        else:
            self._validate_policy_removal(
                environment,
                policies,
                default_branch,
                removal,
            )
        policy_missing = environment is None or (
            policies is not None and policies.get("total_count") == 0
        )
        actions: list[str] = []
        if removal is not None:
            actions.append(
                "remove-deployment-policy:"
                f"id={removal.policy_id},"
                f"name={removal.expected_name},"
                f"type={removal.expected_type}"
            )
        if not immutable_releases_enabled:
            actions.append("enable-immutable-releases")
        if pages is None:
            actions.append("create-pages-workflow-source")
        if environment is None:
            actions.append("create-github-pages-environment")
        if policy_missing:
            actions.append("allow-default-branch-only")

        if dry_run:
            return GitHubPagesConfiguration(
                self.profile.repository,
                default_branch,
                self.profile.workflow,
                "planned",
                tuple(actions),
            )

        if removal is not None:
            self._delete_policy(policy_endpoint, removal)
            verified_cleanup_environment = self._get_required(
                environment_endpoint,
                label="github-pages environment after policy removal",
            )
            verified_cleanup_policies = self._get_required(
                f"{policy_endpoint}?per_page=100",
                label="github-pages deployment policies after policy removal",
            )
            self._validate_environment(
                verified_cleanup_environment,
                verified_cleanup_policies,
                default_branch,
            )

        if not immutable_releases_enabled:
            self._enable_immutable_releases()
        if pages is None:
            self._write_api(
                "POST",
                pages_endpoint,
                {"build_type": "workflow"},
                label="create Pages site",
            )
        if environment is None:
            self._write_api(
                "PUT",
                environment_endpoint,
                {
                    "deployment_branch_policy": {
                        "protected_branches": False,
                        "custom_branch_policies": True,
                    }
                },
                label="create github-pages environment",
            )
        if policy_missing:
            self._write_api(
                "POST",
                policy_endpoint,
                {"name": default_branch, "type": "branch"},
                label="create default-branch deployment policy",
            )

        self._require_immutable_releases_enabled()
        verified_pages = self._get_required(pages_endpoint, label="Pages site")
        verified_environment = self._get_required(
            environment_endpoint,
            label="github-pages environment",
        )
        verified_policies = self._get_required(
            f"{policy_endpoint}?per_page=100",
            label="github-pages deployment policies",
        )
        self._validate_pages(verified_pages)
        self._validate_environment(
            verified_environment,
            verified_policies,
            default_branch,
        )
        return GitHubPagesConfiguration(
            self.profile.repository,
            default_branch,
            self.profile.workflow,
            "configured" if actions else "ready",
            tuple(actions),
        )

    @staticmethod
    def _policy_removal(
        policy_id: int | None,
        expected_name: str | None,
        expected_type: str | None,
    ) -> _PolicyRemoval | None:
        values = (policy_id, expected_name, expected_type)
        if all(value is None for value in values):
            return None
        if any(value is None for value in values):
            raise DeployExecutionError(
                "policy removal requires --remove-policy-id, "
                "--expected-policy-name, and --expected-policy-type together"
            )
        if (
            isinstance(policy_id, bool)
            or not isinstance(policy_id, int)
            or policy_id < 1
        ):
            raise DeployExecutionError("policy removal ID must be a positive integer")
        if (
            not isinstance(expected_name, str)
            or not expected_name
            or expected_name != expected_name.strip()
            or any(ord(char) < 32 for char in expected_name)
        ):
            raise DeployExecutionError(
                "expected policy name must be a non-empty exact name"
            )
        if expected_type not in {"branch", "tag"}:
            raise DeployExecutionError(
                "expected policy type must be exactly branch or tag"
            )
        return _PolicyRemoval(policy_id, expected_name, expected_type)

    def _validate_policy_removal(
        self,
        environment: dict[str, Any] | None,
        policies: dict[str, Any] | None,
        default_branch: str,
        removal: _PolicyRemoval,
    ) -> None:
        if environment is None or policies is None:
            raise DeployExecutionError(
                "policy removal requires an existing github-pages environment"
            )
        self._validate_environment_settings(environment)
        records = self._policy_records(policies)
        identified: list[tuple[int, str, str]] = []
        for record in records:
            policy_id = record.get("id")
            name = record.get("name")
            # Deletion is destructive, so the legacy read-only convention
            # that treats an omitted type as ``branch`` is not sufficient
            # evidence here. GitHub must return the type explicitly.
            policy_type = record.get("type")
            if (
                isinstance(policy_id, bool)
                or not isinstance(policy_id, int)
                or policy_id < 1
                or not isinstance(name, str)
                or policy_type not in {"branch", "tag"}
            ):
                raise DeployExecutionError(
                    "github-pages deployment policy records must contain valid "
                    "positive numeric IDs, names, and explicit types before "
                    "removal"
                )
            identified.append((policy_id, name, policy_type))

        selected = [record for record in identified if record[0] == removal.policy_id]
        if len(selected) != 1:
            raise DeployExecutionError(
                "policy removal ID must identify exactly one deployment policy"
            )
        actual = selected[0]
        expected = (
            removal.policy_id,
            removal.expected_name,
            removal.expected_type,
        )
        if actual != expected:
            raise DeployExecutionError(
                "deployment policy does not exactly match the expected ID, "
                "name, and type; refusing removal"
            )
        if actual[1:] == (default_branch, "branch"):
            raise DeployExecutionError(
                "refusing to remove the exact default-branch deployment policy"
            )
        remaining = [record[1:] for record in identified if record[0] != actual[0]]
        if remaining != [(default_branch, "branch")]:
            raise DeployExecutionError(
                "policy removal must leave exactly the default-branch policy"
            )

    def _delete_policy(
        self,
        policy_endpoint: str,
        removal: _PolicyRemoval,
    ) -> None:
        endpoint = f"{policy_endpoint}/{removal.policy_id}"
        try:
            self._run("api", "--method", "DELETE", endpoint)
        except DeployExecutionError as exc:
            raise DeployExecutionError(
                "cannot remove the exact github-pages deployment policy: " f"{exc}"
            ) from exc

    def _verify_workflow(self, trusted_sha: str) -> None:
        relative = Path(".github") / "workflows" / self.profile.workflow
        workflow = self.repo_root / relative
        if not workflow.is_file() or workflow.is_symlink():
            raise DeployExecutionError(
                f"trusted Pages workflow does not exist: {relative}"
            )
        self._git("cat-file", "-e", f"{trusted_sha}:{relative.as_posix()}")

    def _get_optional(
        self,
        endpoint: str,
        *,
        label: str,
    ) -> dict[str, Any] | None:
        result = self._run("api", endpoint, check=False)
        if result.returncode != 0:
            detail = (result.stderr or result.stdout).strip()
            if re.search(r"(?:HTTP\s+404|\b404\s+Not Found\b)", detail, re.I):
                return None
            raise DeployExecutionError(
                f"cannot inspect {label}" + (f": {detail}" if detail else "")
            )
        return self._json_object(result.stdout, label=label)

    def _get_required(self, endpoint: str, *, label: str) -> dict[str, Any]:
        value = self._get_optional(endpoint, label=label)
        if value is None:
            raise DeployExecutionError(f"{label} is missing after configuration")
        return value

    def _write_api(
        self,
        method: str,
        endpoint: str,
        value: dict[str, Any],
        *,
        label: str,
    ) -> None:
        try:
            self._run(
                "api",
                "--method",
                method,
                endpoint,
                "--input",
                "-",
                input_value=value,
            )
        except DeployExecutionError as exc:
            raise DeployExecutionError(f"cannot {label}: {exc}") from exc

    @staticmethod
    def _json_object(value: str, *, label: str) -> dict[str, Any]:
        try:
            parsed = json.loads(value)
        except json.JSONDecodeError as exc:
            raise DeployExecutionError(f"GitHub returned invalid {label} JSON") from exc
        if not isinstance(parsed, dict):
            raise DeployExecutionError(f"GitHub {label} JSON must be an object")
        return parsed

    @staticmethod
    def _validate_pages(value: dict[str, Any] | None) -> None:
        if value is None:
            return
        if value.get("build_type") != "workflow":
            raise DeployExecutionError(
                "existing Pages site is not workflow-based; refusing to overwrite it"
            )
        if value.get("cname") not in {None, ""}:
            raise DeployExecutionError(
                "existing Pages site uses a custom domain; refusing to overwrite it"
            )

    @staticmethod
    def _validate_environment_settings(environment: dict[str, Any]) -> None:
        deployment_policy = environment.get("deployment_branch_policy")
        if not isinstance(deployment_policy, dict) or deployment_policy != {
            "protected_branches": False,
            "custom_branch_policies": True,
        }:
            raise DeployExecutionError(
                "github-pages environment does not use exact custom branch "
                "policies; refusing to overwrite it"
            )

    @staticmethod
    def _policy_records(
        policies: dict[str, Any] | None,
    ) -> tuple[dict[str, Any], ...]:
        if not isinstance(policies, dict):
            raise DeployExecutionError(
                "github-pages deployment policy response is invalid"
            )
        total = policies.get("total_count")
        records = policies.get("branch_policies")
        if (
            isinstance(total, bool)
            or not isinstance(total, int)
            or total < 0
            or not isinstance(records, list)
            or total != len(records)
        ):
            raise DeployExecutionError(
                "github-pages deployment policy response is incomplete"
            )
        for record in records:
            if not isinstance(record, dict):
                raise DeployExecutionError(
                    "github-pages deployment policy response is invalid"
                )
            name = record.get("name")
            policy_type = record.get("type", "branch")
            if not isinstance(name, str) or policy_type not in {"branch", "tag"}:
                raise DeployExecutionError(
                    "github-pages deployment policy response is invalid"
                )
        return tuple(records)

    @classmethod
    def _validate_environment(
        cls,
        environment: dict[str, Any] | None,
        policies: dict[str, Any] | None,
        default_branch: str,
        *,
        allow_missing_default_policy: bool = False,
    ) -> None:
        if environment is None:
            if policies is not None:
                raise DeployExecutionError(
                    "deployment policies exist without a github-pages environment"
                )
            return
        cls._validate_environment_settings(environment)
        records = cls._policy_records(policies)
        normalized = [
            (record["name"], record.get("type", "branch")) for record in records
        ]
        if allow_missing_default_policy and not normalized:
            return
        if normalized != [(default_branch, "branch")]:
            raise DeployExecutionError(
                "github-pages environment must allow only the exact default "
                "branch; refusing to overwrite existing policies"
            )


__all__ = ["GitHubPagesConfiguration", "GitHubPagesConfigurator"]
