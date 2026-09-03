"""Errors raised by the local Comparator SDK."""

from __future__ import annotations

from reasbook_sdk_common import SdkError


class ComparatorError(SdkError):
    """Base class for expected Comparator SDK failures."""


class ComparatorConfigError(ComparatorError):
    """The project or Comparator configuration is invalid."""


class ComparatorExecutionError(ComparatorError):
    """Comparator or one of its preparation commands could not run."""


class ComparatorTimeoutError(ComparatorExecutionError):
    """Comparator exceeded its configured execution deadline."""


# Short aliases keep call sites concise while retaining descriptive names.
ConfigError = ComparatorConfigError
ExecutionError = ComparatorExecutionError

__all__ = [
    "ComparatorConfigError",
    "ComparatorError",
    "ComparatorExecutionError",
    "ComparatorTimeoutError",
    "ConfigError",
    "ExecutionError",
]
