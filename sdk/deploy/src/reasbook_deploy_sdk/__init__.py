"""Composable deployment orchestration for ReasBook projects."""

from .errors import DeployConfigError, DeployError, DeployExecutionError
from .docker import DockerDeploymentConfig, deploy_static
from .git import (
    GitClient,
    PROJECT_ID_RE,
    VERSION_BRANCH_RE,
    project_source_rel,
    version_key,
    working_tree_fingerprint,
)
from .models import BookBuildResult, BuildResult, DeploymentConfig, DeploymentReport
from .pipeline import (
    CallableStage,
    ComparatorStage,
    DeploymentPipeline,
    StageResult,
    TheoremGraphStage,
    VersoStage,
)
from .reviewer import ReviewIndexSpec, ReviewerAdapter, reviewer_environment
from .runtime import (
    DEFAULT_CACHE_ROOT,
    default_cache_root,
    deployment_lock,
    ensure_toolchain,
    find_elan,
    find_python,
    lake_environment,
    prepare_cache_dirs,
    prepare_external_lake,
    prepare_project_runtime,
    read_env_defaults,
    resolve_path,
    run_command,
    safe_name,
    timeout_from_env,
    write_json,
)
from .service import DEFAULT_BOOKS, DeploymentService, cache_identity, launch_reviewer, utc_now

__version__ = "0.1.0"

__all__ = [
    "BookBuildResult",
    "BuildResult",
    "DEFAULT_BOOKS",
    "DeployConfigError",
    "DeployError",
    "DeployExecutionError",
    "DockerDeploymentConfig",
    "DeploymentConfig",
    "DeploymentReport",
    "DeploymentService",
    "DeploymentPipeline",
    "GitClient",
    "PROJECT_ID_RE",
    "ReviewIndexSpec",
    "ReviewerAdapter",
    "CallableStage",
    "ComparatorStage",
    "DEFAULT_CACHE_ROOT",
    "StageResult",
    "TheoremGraphStage",
    "VersoStage",
    "VERSION_BRANCH_RE",
    "deployment_lock",
    "default_cache_root",
    "deploy_static",
    "cache_identity",
    "ensure_toolchain",
    "find_elan",
    "find_python",
    "lake_environment",
    "launch_reviewer",
    "prepare_cache_dirs",
    "prepare_external_lake",
    "prepare_project_runtime",
    "project_source_rel",
    "read_env_defaults",
    "resolve_path",
    "reviewer_environment",
    "run_command",
    "safe_name",
    "timeout_from_env",
    "utc_now",
    "version_key",
    "working_tree_fingerprint",
    "write_json",
]
