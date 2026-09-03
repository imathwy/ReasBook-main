"""Small, platform-neutral primitives shared by the ReasBook SDKs."""

from .command import (
    Command,
    CommandExecutionError,
    CommandResult,
    CommandRunner,
    CommandRunnerProtocol,
    CommandTimeoutError,
    merged_environment,
    normalize_environment,
)
from .errors import SdkError
from .paths import (
    atomic_write_json,
    atomic_write_text,
    ensure_absolute,
    ensure_within,
    safe_relative,
)

__all__ = [
    "Command",
    "CommandExecutionError",
    "CommandResult",
    "CommandRunner",
    "CommandRunnerProtocol",
    "CommandTimeoutError",
    "SdkError",
    "atomic_write_json",
    "atomic_write_text",
    "ensure_absolute",
    "ensure_within",
    "merged_environment",
    "normalize_environment",
    "safe_relative",
]

__version__ = "0.1.0"
