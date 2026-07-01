"""Filesystem policy for the isolated experiment project."""

from __future__ import annotations

from dataclasses import dataclass
from pathlib import Path


@dataclass(frozen=True)
class PolicyDecision:
    decision: str
    reason: str
    resolved_path: str


class WritePolicy:
    """Allow persistent writes only below one resolved project directory."""

    def __init__(self, repository_root: Path, writable_root: Path) -> None:
        self.repository_root = repository_root.resolve(strict=True)
        self.writable_root = writable_root.resolve(strict=True)
        if not self.writable_root.is_relative_to(self.repository_root):
            raise ValueError("writable root must be inside repository root")

    def decide(self, requested_path: Path) -> PolicyDecision:
        candidate = requested_path
        if not candidate.is_absolute():
            candidate = self.repository_root / candidate
        resolved = candidate.resolve(strict=False)
        if resolved == self.writable_root or resolved.is_relative_to(self.writable_root):
            return PolicyDecision("allow", "path is inside isolated writable root", str(resolved))
        return PolicyDecision("deny", "path is outside isolated writable root", str(resolved))


def decide_action(action: str, *, approved: bool = False) -> PolicyDecision:
    """Classify non-filesystem actions that need explicit human authority."""
    approval_actions = {"network", "publish", "commit", "push", "delete", "high-cost"}
    denied_actions = {"read-secret", "write-source-project"}
    if action in denied_actions:
        return PolicyDecision("deny", f"{action} is always forbidden", action)
    if action in approval_actions and not approved:
        return PolicyDecision("approval-required", f"{action} requires explicit approval", action)
    if action in approval_actions:
        return PolicyDecision("allow", f"{action} was explicitly approved", action)
    if action == "dry-run":
        return PolicyDecision(
            "dry-run-only", "task may produce a preview but may not execute", action
        )
    return PolicyDecision("allow", "low-risk local action", action)
