"""Standalone, transport-neutral SDK for running Lean Comparator locally."""

from .commands import build_command, cache_command, compare_command, request_from_config
from .config import ComparatorConfig, validate_comparator_data, validate_comparator_json
from .errors import (
    ComparatorConfigError,
    ComparatorError,
    ComparatorExecutionError,
    ComparatorTimeoutError,
)
from .models import ComparisonResult, ComparatorRequest
from .project import (
    LakeProject,
    discover_comparator_root,
    discover_project,
    expected_olean,
    split_module_name,
    verify_module_outputs,
)
from .runner import ComparatorRunner

__version__ = "0.1.0"

__all__ = [
    "ComparatorConfig",
    "ComparatorConfigError",
    "ComparatorError",
    "ComparatorExecutionError",
    "ComparatorRequest",
    "ComparatorRunner",
    "ComparatorTimeoutError",
    "ComparisonResult",
    "LakeProject",
    "build_command",
    "cache_command",
    "compare_command",
    "discover_comparator_root",
    "discover_project",
    "expected_olean",
    "request_from_config",
    "split_module_name",
    "validate_comparator_data",
    "validate_comparator_json",
    "verify_module_outputs",
]
