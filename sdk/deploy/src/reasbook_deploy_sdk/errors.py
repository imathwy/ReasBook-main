"""Errors raised by the deployment orchestration SDK."""

from __future__ import annotations

from reasbook_sdk_common import SdkError


class DeployError(SdkError):
    """Base class for expected deployment failures."""


class DeployConfigError(DeployError):
    """Deployment inputs are missing or unsafe."""


class DeployExecutionError(DeployError):
    """An external deployment command failed."""


__all__ = ["DeployConfigError", "DeployError", "DeployExecutionError"]
