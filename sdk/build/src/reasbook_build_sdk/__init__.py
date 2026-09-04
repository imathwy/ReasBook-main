"""Platform-independent planning and execution tools for ReasBook builds."""

from .command import Command, CommandResult, CommandRunner
from .config import load_build_options
from .docs import (
    ProjectDocumentationBuilder,
    ProjectDocsResult,
    ProjectOleanInspection,
    ReachableProjectModule,
    ReachableProjectModulePlan,
    inspect_project_olean,
    plan_reachable_project_modules,
    project_olean_candidates,
)
from .errors import (
    BuildFailed,
    BuildSdkError,
    CommandError,
    ConfigurationError,
    ProjectError,
)
from .executor import CallableRunner, SubprocessRunner
from .lake import build_command, cache_command, plan_build, shell_preview
from .models import BuildOptions, BuildPlan, BuildResult
from .project import LakeProject, discover_project, first_artifact
from .service import BuildExecutor, BuildService, DryRunExecutor, LocalBuildExecutor
from .targets import (
    library_target,
    parse_library_declarations,
    parse_library_declarations_text,
    parse_library_roots_text,
    project_doc_targets,
    selected_targets,
    target_from_declarations,
)

__all__ = [
    "BuildExecutor",
    "BuildFailed",
    "BuildOptions",
    "BuildPlan",
    "BuildResult",
    "BuildSdkError",
    "BuildService",
    "CallableRunner",
    "Command",
    "CommandError",
    "CommandResult",
    "CommandRunner",
    "ConfigurationError",
    "DryRunExecutor",
    "LakeProject",
    "LocalBuildExecutor",
    "ProjectError",
    "ProjectDocumentationBuilder",
    "ProjectDocsResult",
    "ProjectOleanInspection",
    "ReachableProjectModule",
    "ReachableProjectModulePlan",
    "SubprocessRunner",
    "build_command",
    "cache_command",
    "discover_project",
    "first_artifact",
    "inspect_project_olean",
    "load_build_options",
    "library_target",
    "parse_library_declarations",
    "parse_library_declarations_text",
    "parse_library_roots_text",
    "plan_build",
    "plan_reachable_project_modules",
    "project_doc_targets",
    "project_olean_candidates",
    "selected_targets",
    "shell_preview",
    "target_from_declarations",
]

__version__ = "0.1.0"
