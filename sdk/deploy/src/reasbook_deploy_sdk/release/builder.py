"""Parallel execution of planned release branches."""

from __future__ import annotations

from concurrent.futures import ThreadPoolExecutor, as_completed
from contextlib import contextmanager
import fcntl
import os
from pathlib import Path
import shutil
import sys
import threading
import uuid
from typing import Iterator

from reasbook_sdk_common import (
    Command,
    CommandExecutionError,
    CommandRunner,
)

from ..errors import DeployExecutionError
from ..git import version_key
from ..runtime import safe_name
from .build_plan import (
    BranchBuildPlan,
    BranchPlanFactory,
    BranchStep,
    ReleaseBuildOptions,
)
from .models import ReleaseSpec
from .results import BranchBuildResult, ReleaseBuildReport, StageOutcome
from .store import ReleaseLayout
from .worktree import ReleaseWorktreeManager


class LocalReleaseBuilder:
    """Build branches in parallel while preserving per-branch stage order."""

    def __init__(
        self,
        repo_root: Path,
        tooling_root: Path,
        cache_root: Path,
        layout: ReleaseLayout,
        *,
        options: ReleaseBuildOptions | None = None,
        worktrees: ReleaseWorktreeManager | None = None,
    ) -> None:
        self.repo_root = Path(repo_root).expanduser().resolve()
        self.tooling_root = Path(tooling_root).expanduser().resolve()
        self.cache_root = Path(cache_root).expanduser().resolve()
        self.layout = layout
        self.options = options or ReleaseBuildOptions()
        self.worktrees = worktrees or ReleaseWorktreeManager(self.repo_root, layout)
        self.plan_factory = BranchPlanFactory(
            self.tooling_root,
            self.cache_root,
            layout,
            self.options,
        )
        self._runner_lock = threading.Lock()
        self._active_runners: list[CommandRunner] = []

    def build(self, spec: ReleaseSpec) -> ReleaseBuildReport:
        plans = self.plan(spec, prepare_worktrees=True)
        results = self._run_plans(plans)
        ordered = tuple(
            results[branch.name]
            for branch in sorted(spec.branches, key=lambda item: version_key(item.name))
        )
        return ReleaseBuildReport.from_branches(spec, ordered)

    def plan(
        self,
        spec: ReleaseSpec,
        *,
        prepare_worktrees: bool = False,
    ) -> list[BranchBuildPlan]:
        return [
            self.plan_factory.create(
                spec,
                branch,
                (
                    self.worktrees.prepare(spec, branch)
                    if prepare_worktrees
                    else self.layout.worktrees / safe_name(branch.name)
                ),
            )
            for branch in spec.branches
        ]

    def _run_plans(
        self,
        plans: list[BranchBuildPlan],
    ) -> dict[str, BranchBuildResult]:
        results: dict[str, BranchBuildResult] = {}
        workers = min(self.options.max_parallel_branches, len(plans))
        pool = ThreadPoolExecutor(max_workers=workers)
        try:
            futures = {pool.submit(self._run_branch, plan): plan for plan in plans}
            for future in as_completed(futures):
                plan = futures[future]
                try:
                    results[plan.branch.name] = future.result()
                except Exception as exc:
                    results[plan.branch.name] = BranchBuildResult(
                        plan.branch.name,
                        plan.branch.commit,
                        "failed",
                        None,
                        (),
                        str(exc),
                    )
        except BaseException:
            self._terminate_active()
            pool.shutdown(wait=True, cancel_futures=True)
            raise
        else:
            pool.shutdown(wait=True)
        return results

    def _run_branch(self, plan: BranchBuildPlan) -> BranchBuildResult:
        with self._branch_cache_lock(plan):
            return self._run_branch_locked(plan)

    def _run_branch_locked(self, plan: BranchBuildPlan) -> BranchBuildResult:
        outcomes: list[StageOutcome] = []
        degraded = False
        for index, step in enumerate(plan.steps, start=1):
            log = (
                self.layout.logs
                / safe_name(plan.branch.name)
                / f"{index:02d}-{safe_name(step.name)}.log"
            )
            print(
                f"[release][{plan.branch.name}] start {step.name}; log: {log}",
                file=sys.stderr,
                flush=True,
            )
            outcome = self._run_step(
                step,
                log,
            )
            print(
                f"[release][{plan.branch.name}] {step.name}: {outcome.status}",
                file=sys.stderr,
                flush=True,
            )
            outcomes.append(outcome)
            if outcome.status != "failed":
                continue
            if step.required:
                return self._failed_result(plan, outcomes, outcome.message)
            degraded = degraded or step.name != "cache"
        try:
            self._publish_branch_site(plan)
        except (OSError, DeployExecutionError) as exc:
            outcomes.append(StageOutcome("stage-site", "failed", str(exc)))
            return self._failed_result(plan, outcomes, str(exc))
        outcomes.append(StageOutcome("stage-site", "success"))
        return BranchBuildResult(
            plan.branch.name,
            plan.branch.commit,
            "degraded" if degraded else "success",
            str(plan.published_site),
            tuple(outcomes),
        )

    @contextmanager
    def _branch_cache_lock(self, plan: BranchBuildPlan) -> Iterator[None]:
        lock = (
            self.cache_root
            / "locks"
            / (
                f"release-{safe_name(plan.branch.name)}-"
                f"{plan.branch.commit[:12]}-"
                f"{plan.branch.lake_manifest_sha256[-12:]}.lock"
            )
        )
        lock.parent.mkdir(parents=True, exist_ok=True)
        with lock.open("a+", encoding="utf-8") as handle:
            fcntl.flock(handle.fileno(), fcntl.LOCK_EX)
            try:
                yield
            finally:
                fcntl.flock(handle.fileno(), fcntl.LOCK_UN)

    @staticmethod
    def _failed_result(
        plan: BranchBuildPlan,
        outcomes: list[StageOutcome],
        error: str,
    ) -> BranchBuildResult:
        return BranchBuildResult(
            plan.branch.name,
            plan.branch.commit,
            "failed",
            None,
            tuple(outcomes),
            error,
        )

    def _run_step(self, step: BranchStep, log: Path) -> StageOutcome:
        log.parent.mkdir(parents=True, exist_ok=True)
        runner = CommandRunner(output_file=log)
        with self._runner_lock:
            self._active_runners.append(runner)
        try:
            result = runner.run(
                Command(
                    step.argv,
                    cwd=step.cwd,
                    env=step.env,
                    timeout=step.timeout,
                )
            )
        except CommandExecutionError as exc:
            return StageOutcome(step.name, "failed", str(exc), str(log))
        finally:
            with self._runner_lock:
                self._active_runners = [
                    item for item in self._active_runners if item is not runner
                ]
        if result.returncode != 0:
            return StageOutcome(
                step.name,
                "failed",
                f"command exited {result.returncode}",
                str(log),
            )
        return StageOutcome(step.name, "success", log=str(log))

    def _terminate_active(self) -> None:
        with self._runner_lock:
            runners = tuple(self._active_runners)
        for runner in runners:
            runner.terminate()

    @staticmethod
    def _publish_branch_site(plan: BranchBuildPlan) -> None:
        source = plan.source_site
        if not (source / "index.html").is_file():
            raise DeployExecutionError(f"branch site has no index.html: {source}")
        symlink = next(
            (path for path in source.rglob("*") if path.is_symlink()),
            None,
        )
        if symlink is not None:
            raise DeployExecutionError(f"branch site contains a symlink: {symlink}")
        target = plan.published_site
        if target.parent.is_symlink():
            raise DeployExecutionError(
                f"branch site directory is a symlink: {target.parent}"
            )
        target.parent.mkdir(parents=True, exist_ok=True)
        staged = target.parent / f".site-{uuid.uuid4().hex}"
        shutil.copytree(source, staged)
        backup = target.parent / f".site-backup-{uuid.uuid4().hex}"
        had_target = target.exists()
        if had_target:
            os.replace(target, backup)
        try:
            os.replace(staged, target)
        except OSError:
            if had_target and not target.exists():
                os.replace(backup, target)
            raise
        if had_target:
            shutil.rmtree(backup)


__all__ = ["LocalReleaseBuilder"]
