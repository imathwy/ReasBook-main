"""Standalone, transport-neutral Verso build SDK."""

from .builder import VersoBuildResult, VersoBuilder
from .commands import CommandSpec, clean_environment, lake_argv, pipeline
from .config import LEAN_ENV_NAMES, VersoBuildConfig
from .errors import CommandExecutionError, ProjectValidationError, VersoBuildError
from .project import VersoProject, discover_project
from .runner import CommandResult, CommandRunner, SubprocessRunner

__version__ = "0.1.0"

__all__ = [
    "CommandExecutionError",
    "CommandResult",
    "CommandRunner",
    "CommandSpec",
    "LEAN_ENV_NAMES",
    "ProjectValidationError",
    "SubprocessRunner",
    "VersoBuildConfig",
    "VersoBuildError",
    "VersoBuildResult",
    "VersoBuilder",
    "VersoProject",
    "clean_environment",
    "discover_project",
    "lake_argv",
    "pipeline",
]
