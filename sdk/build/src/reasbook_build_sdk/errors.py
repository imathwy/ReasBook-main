"""Exception hierarchy for the ReasBook build SDK.

The SDK deliberately keeps errors independent of the transport used to run a
build.  A caller can therefore replace the local executor without having to
translate platform-specific exceptions throughout the application.
"""

from __future__ import annotations


class BuildSdkError(Exception):
    """Base class for all expected SDK errors."""


class ProjectError(BuildSdkError):
    """The requested project is not a valid Lake project."""


class ConfigurationError(BuildSdkError):
    """Build options are missing or malformed."""


class CommandError(BuildSdkError):
    """A command could not be started by an executor."""


class BuildFailed(BuildSdkError):
    """A build command returned a non-zero status."""
