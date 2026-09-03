"""Adapters for publishing generated data into the ReasBook reviewer."""

from __future__ import annotations

from dataclasses import dataclass
import json
import os
from pathlib import Path
from typing import Mapping

from reasbook_sdk_common import ensure_within

from .errors import DeployConfigError, DeployExecutionError
from .runtime import Runner, run_command


@dataclass(frozen=True)
class ReviewIndexSpec:
    """Inputs for the reviewer's lightweight, source-only index builder."""

    project_root: Path
    output: Path
    source_output: Path
    slug: str
    kind: str
    module_prefix: str
    branch: str
    commit: str
    source_label: str
    max_items: int = 0


class ReviewerAdapter:
    """Invoke reviewer-owned scripts without importing their application code."""

    def __init__(
        self,
        reviewer_root: str | Path,
        *,
        python_bin: str,
        output_root: str | Path | None = None,
        runner: Runner | None = None,
    ) -> None:
        self.reviewer_root = Path(reviewer_root).expanduser().resolve()
        self.python_bin = python_bin
        self.output_root = (
            Path(output_root).expanduser().resolve() if output_root is not None else None
        )
        self.runner = runner

    def _output_path(self, path: Path) -> Path:
        if self.output_root is None:
            return path
        try:
            return ensure_within(path, self.output_root, field="reviewer output")
        except ValueError as exc:
            raise DeployConfigError(str(exc)) from exc

    def _script(self, name: str) -> Path:
        path = self.reviewer_root / "scripts" / name
        if not path.is_file():
            raise DeployConfigError(f"reviewer script is missing: {path}")
        return path

    def _script_for_plan(self, name: str, *, dry_run: bool) -> Path:
        path = self.reviewer_root / "scripts" / name
        if not dry_run:
            return self._script(name)
        return path

    def build_index(self, spec: ReviewIndexSpec, *, dry_run: bool = False) -> None:
        if spec.max_items < 0:
            raise DeployConfigError("max_items must not be negative")
        output = self._output_path(spec.output)
        source_output = self._output_path(spec.source_output)
        command: list[str] = [
            self.python_bin,
            str(self._script_for_plan("build_review_index.py", dry_run=dry_run)),
            "--project-root",
            str(spec.project_root),
            "--output",
            str(output),
            "--source-output",
            str(source_output),
            "--slug",
            spec.slug,
            "--kind",
            spec.kind,
            "--module-prefix",
            spec.module_prefix,
            "--branch",
            spec.branch,
            "--commit",
            spec.commit,
            "--source-label",
            spec.source_label,
        ]
        if spec.max_items:
            command.extend(("--max-items", str(spec.max_items)))
        run_command(
            command,
            runner=self.runner,
            cwd=self.reviewer_root,
            dry_run=dry_run,
        )
        if not dry_run:
            self._validate_index(output, spec.slug, source_output)

    @staticmethod
    def _read_object(path: Path, label: str) -> dict[str, object]:
        try:
            value = json.loads(path.read_text(encoding="utf-8"))
        except (OSError, json.JSONDecodeError) as exc:
            raise DeployExecutionError(f"{label} is not valid JSON: {path}") from exc
        if not isinstance(value, dict):
            raise DeployExecutionError(f"{label} must be a JSON object: {path}")
        return value

    def _validate_index(self, output: Path, slug: str, source_output: Path) -> None:
        payload = self._read_object(output, "review index")
        if payload.get("schemaVersion") != 1 or payload.get("bookSlug") != slug:
            raise DeployExecutionError(
                f"review index has an incompatible schema or slug: {output}"
            )
        if not isinstance(payload.get("items"), list):
            raise DeployExecutionError(f"review index items must be an array: {output}")
        source = self._read_object(source_output, "source manifest")
        if not isinstance(source.get("files"), list):
            raise DeployExecutionError(
                f"source manifest files must be an array: {source_output}"
            )

    def regenerate_catalog(
        self,
        *,
        reasbook_root: Path,
        output: Path,
        data_root: Path,
        stacks_root: Path | None = None,
        include_papers: bool = False,
        dry_run: bool = False,
    ) -> None:
        output = self._output_path(output)
        data_root = Path(data_root).expanduser().resolve()
        if self.output_root is not None:
            try:
                ensure_within(data_root, self.output_root, field="reviewer data")
            except ValueError as exc:
                raise DeployConfigError(str(exc)) from exc
        command: list[str] = [
            self.python_bin,
            str(self._script_for_plan("discover_catalog.py", dry_run=dry_run)),
            "--reasbook-root",
            str(reasbook_root),
            "--output",
            str(output),
            "--data-root",
            str(data_root),
            "--stamp",
        ]
        if include_papers:
            command.append("--include-papers")
        if stacks_root is not None and stacks_root.is_dir():
            command.extend(("--include-stacks", "--stacks-root", str(stacks_root)))
        run_command(
            command,
            runner=self.runner,
            cwd=self.reviewer_root,
            dry_run=dry_run,
        )
        if not dry_run:
            payload = self._read_object(output, "reviewer catalog")
            if not isinstance(payload.get("books"), list):
                raise DeployExecutionError(
                    f"reviewer catalog books must be an array: {output}"
                )


def reviewer_environment(
    *,
    repo_root: Path,
    data_root: Path,
    host: str,
    port: int,
    python_bin: str,
    base: Mapping[str, str] | None = None,
) -> dict[str, str]:
    """Build the explicit environment passed to ``start_server.sh``."""

    environment = dict(os.environ if base is None else base)
    environment.update(
        {
            "REASBOOK_ROOT": str(repo_root),
            "REASBOOK_REVIEWER_DATA": str(data_root),
            "REASBOOK_REVIEWER_CATALOG": str(data_root / "catalog.json"),
            "REASBOOK_REVIEWER_HOST": host,
            "REASBOOK_REVIEWER_PORT": str(port),
            "REASBOOK_REVIEWER_PYTHON": python_bin,
        }
    )
    return environment


__all__ = [
    "ReviewIndexSpec",
    "ReviewerAdapter",
    "reviewer_environment",
]
