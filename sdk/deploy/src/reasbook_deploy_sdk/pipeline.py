"""Composable deployment stages for the four capability SDKs."""

from __future__ import annotations

from dataclasses import dataclass
from pathlib import Path
from typing import Any, Callable, Mapping, Protocol, Sequence


StageStatus = str


@dataclass(frozen=True)
class StageResult:
    """Normalized outcome returned by one deployment stage."""

    name: str
    status: StageStatus
    message: str = ""
    value: Any = None

    @property
    def succeeded(self) -> bool:
        return self.status in {"success", "planned", "skipped"}

    def public_dict(self) -> dict[str, Any]:
        value = _json_value(self.value)
        return {
            "name": self.name,
            "status": self.status,
            "message": self.message,
            "value": value,
        }


def _json_value(value: Any) -> Any:
    """Keep stage reports serializable even for injected adapters."""

    if value is None or isinstance(value, (str, int, float, bool)):
        return value
    if isinstance(value, Path):
        return str(value)
    if hasattr(value, "public_dict"):
        return _json_value(value.public_dict())
    if isinstance(value, Mapping):
        return {str(key): _json_value(item) for key, item in value.items()}
    if isinstance(value, (list, tuple, set)):
        return [_json_value(item) for item in value]
    return str(value)


class Stage(Protocol):
    """Driving port implemented by a deployment stage."""

    name: str

    def run(self, *, dry_run: bool = False) -> StageResult:
        ...


@dataclass
class CallableStage:
    """Adapt a small use-case callable to the stage port."""

    name: str
    callback: Callable[[bool], Any]

    def run(self, *, dry_run: bool = False) -> StageResult:
        value = self.callback(dry_run)
        return StageResult(
            self.name,
            "planned" if dry_run else "success",
            value=value,
        )


@dataclass
class VersoStage:
    """Adapter for :class:`verso_build_sdk.VersoBuilder`."""

    builder: Any
    name: str = "verso"

    def run(self, *, dry_run: bool = False) -> StageResult:
        result = self.builder.run(dry_run=dry_run)
        return StageResult(self.name, "planned" if dry_run else "success", value=result)


@dataclass
class TheoremGraphStage:
    """Adapter for :class:`theorem_graph_sdk.GraphGenerator`."""

    generator: Any
    name: str = "theorem_graph"

    def run(self, *, dry_run: bool = False) -> StageResult:
        if dry_run:
            return StageResult(self.name, "planned")
        return StageResult(self.name, "success", value=self.generator.generate())


@dataclass
class ComparatorStage:
    """Adapter for :class:`comparator_sdk.ComparatorRunner`."""

    comparator: Any
    name: str = "comparator"

    def run(self, *, dry_run: bool = False) -> StageResult:
        result = self.comparator.compare(dry_run=dry_run)
        if dry_run or getattr(result, "status", None) == "planned":
            status = "planned"
        elif getattr(result, "succeeded", False):
            status = "success"
        else:
            status = "failed"
        return StageResult(self.name, status, value=result)


@dataclass
class DeploymentPipeline:
    """Run ordered stages and stop at the first non-success result."""

    stages: Sequence[Stage]

    def plan(self) -> tuple[str, ...]:
        return tuple(stage.name for stage in self.stages)

    def run(self, *, dry_run: bool = False) -> tuple[StageResult, ...]:
        results: list[StageResult] = []
        for stage in self.stages:
            try:
                result = stage.run(dry_run=dry_run)
            except Exception as exc:  # stage boundary translates failures
                result = StageResult(stage.name, "failed", message=str(exc))
            results.append(result)
            if not result.succeeded:
                break
        return tuple(results)


__all__ = [
    "CallableStage",
    "ComparatorStage",
    "DeploymentPipeline",
    "Stage",
    "StageResult",
    "TheoremGraphStage",
    "VersoStage",
]
