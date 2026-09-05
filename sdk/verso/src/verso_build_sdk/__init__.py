"""Standalone, transport-neutral Verso build SDK."""

from .builder import VersoBuildResult, VersoBuilder
from .commands import CommandSpec, clean_environment, lake_argv, pipeline
from .config import LEAN_ENV_NAMES, VersoBuildConfig
from .errors import CommandExecutionError, ProjectValidationError, VersoBuildError
from .literate import (
    LiterateArtifact,
    LiterateCacheBuilder,
    LiterateCacheError,
    LiterateCacheIdentity,
    LiterateCacheResult,
    UnsafeLiterateCacheError,
    load_module_manifest,
)
from .literate_fragments import (
    LiterateFragmentIdentity,
    assemble_fragments,
    partition_modules,
    publish_fragment,
)
from .project import VersoProject, discover_project
from .runner import CommandResult, CommandRunner, SubprocessRunner

__version__ = "0.1.0"

__all__ = [
    "CommandExecutionError",
    "CommandResult",
    "CommandRunner",
    "CommandSpec",
    "LEAN_ENV_NAMES",
    "LiterateArtifact",
    "LiterateCacheBuilder",
    "LiterateCacheError",
    "LiterateCacheIdentity",
    "LiterateCacheResult",
    "LiterateFragmentIdentity",
    "ProjectValidationError",
    "SubprocessRunner",
    "UnsafeLiterateCacheError",
    "VersoBuildConfig",
    "VersoBuildError",
    "VersoBuildResult",
    "VersoBuilder",
    "VersoProject",
    "clean_environment",
    "assemble_fragments",
    "discover_project",
    "lake_argv",
    "load_module_manifest",
    "pipeline",
    "partition_modules",
    "publish_fragment",
]
