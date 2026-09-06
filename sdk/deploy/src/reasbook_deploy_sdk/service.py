"""Use-case orchestration for isolated ReasBook reviewer deployments."""

from __future__ import annotations

from dataclasses import dataclass
from datetime import datetime, timezone
from contextlib import nullcontext
import hashlib
import os
from pathlib import Path
import sys
import time
from typing import Mapping

from reasbook_sdk_common import Command, CommandResult, CommandRunner

from .errors import DeployConfigError, DeployExecutionError
from .git import GitClient, PROJECT_ID_RE, VERSION_BRANCH_RE, working_tree_fingerprint
from .models import BookBuildResult, DeploymentConfig, DeploymentReport
from .pipeline import DeploymentPipeline
from .reviewer import ReviewIndexSpec, ReviewerAdapter, reviewer_environment
from .runtime import (
    Runner,
    deployment_lock,
    ensure_toolchain,
    find_python,
    lake_environment,
    prepare_cache_dirs,
    prepare_external_lake,
    run_command,
    safe_name,
    timeout_from_env,
    write_json,
)
from .transaction import FileTransaction


DEFAULT_BOOKS = ("IntroductiontoRealAnalysisVolumeI_JiriLebl_2025",)


def utc_now() -> str:
    return datetime.now(timezone.utc).isoformat(timespec="seconds").replace("+00:00", "Z")


def cache_identity(root: Path, branch: str, commit: str) -> str:
    """Build a cache key from branch, revision, toolchain, and manifest."""

    toolchain = (
        (root / "lean-toolchain").read_bytes()
        if (root / "lean-toolchain").is_file()
        else b""
    )
    manifest = (
        (root / "lake-manifest.json").read_bytes()
        if (root / "lake-manifest.json").is_file()
        else b""
    )
    digest = hashlib.sha256(toolchain + b"\0" + manifest).hexdigest()[:12]
    revision = safe_name(commit[:12] or "working")
    return f"{safe_name(branch)}-{revision}-{digest}"


class _LoggingRunner:
    """Add per-command logs while delegating execution to the common runner."""

    def __init__(self, delegate: Runner, log_dir: Path, prefix: str) -> None:
        self.delegate = delegate
        self.log_dir = log_dir
        self.prefix = safe_name(prefix)
        self.counter = 0

    def run(self, command: Command) -> CommandResult:
        self.counter += 1
        path = self.log_dir / f"{self.prefix}-{self.counter:02d}.log"
        if isinstance(self.delegate, CommandRunner):
            result = CommandRunner(
                inherit_environment=self.delegate.inherit_environment,
                output_file=path,
            ).run(command)
        else:
            result = self.delegate.run(command)
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text(
                (result.stdout or "") + (result.stderr or ""),
                encoding="utf-8",
            )
        return result


def _build_with_sdk(
    *,
    project_root: Path,
    target: str,
    lake_bin: Path,
    lake_args: tuple[str, ...] = ("-R",),
    environment: Mapping[str, str],
    timeout: float,
    log_dir: Path,
    label: str,
    runner: Runner | None,
    dry_run: bool,
) -> None:
    """Plan and execute a core/docs target through the build SDK."""

    if dry_run:
        run_command(
            (str(lake_bin), *lake_args, "build", target),
            cwd=project_root,
            env=environment,
            timeout=timeout,
            dry_run=True,
        )
        return
    from reasbook_build_sdk import BuildOptions, BuildService, LocalBuildExecutor

    delegate = runner or CommandRunner(stream=False)
    logging_runner = _LoggingRunner(delegate, log_dir, label)
    options = BuildOptions.from_values(
        targets=(target,),
        lake_args=lake_args,
        lake_bin=str(lake_bin),
        run_cache_get=False,
        build_timeout_seconds=timeout,
        environment=environment,
        verify_outputs=False,
    )
    result = BuildService(
        executor=LocalBuildExecutor(runner=logging_runner),
    ).run(project_root, options)
    if not result.succeeded:
        raise DeployExecutionError(f"{label} failed: {result.summary()}")


def _cache_get(
    *,
    project_root: Path,
    target: str,
    lake_bin: Path,
    environment: Mapping[str, str],
    timeout: float,
    log_path: Path,
    runner: Runner | None,
    dry_run: bool,
) -> None:
    """Run optional cache priming and preserve the old non-blocking policy."""

    if dry_run:
        run_command(
            (
                str(lake_bin),
                "-R",
                "exe",
                "cache",
                "get",
                f"Books/{target}/Book.lean",
            ),
            cwd=project_root,
            env=environment,
            timeout=timeout,
            dry_run=True,
        )
        return
    # The build SDK owns Lake command construction; cache failures are warnings
    # because a local build can still produce a useful review index.
    from reasbook_build_sdk.lake import cache_command

    command = cache_command(
        project_root,
        lake_bin=str(lake_bin),
        timeout_seconds=timeout,
        lake_args=("-R",),
        targets=(f"Books/{target}/Book.lean",),
        environment=environment,
    )
    try:
        result = run_command(
            command.argv,
            runner=runner,
            cwd=command.cwd,
            env=command.env,
            timeout=command.timeout,
            log_path=log_path,
            check=False,
            dry_run=dry_run,
        )
    except DeployExecutionError as exc:
        print(f"[deploy] warning: cache get failed for {target}: {exc}", file=sys.stderr)
        return
    if result.returncode:
        print(
            f"[deploy] warning: cache get failed for {target}; continuing with local build",
            file=sys.stderr,
        )


@dataclass
class DeploymentService:
    """Coordinate source selection, builds, indexes, and catalog publication."""

    config: DeploymentConfig
    runner: Runner | None = None
    git: GitClient | None = None
    reviewer: ReviewerAdapter | None = None
    pipeline: DeploymentPipeline | None = None

    def __post_init__(self) -> None:
        self.config = self.config.resolved()
        self.git = self.git or GitClient(runner=self.runner)
        python_bin = self.config.python_bin or sys.executable
        self.reviewer = self.reviewer or ReviewerAdapter(
            self.config.reviewer_root,
            python_bin=python_bin,
            output_root=self.config.data_root,
            runner=self.runner,
        )

    @property
    def _git(self) -> GitClient:
        if self.git is None:
            raise DeployExecutionError("Git adapter is not configured")
        return self.git

    @property
    def _reviewer(self) -> ReviewerAdapter:
        if self.reviewer is None:
            raise DeployExecutionError("reviewer adapter is not configured")
        return self.reviewer

    def validate(self) -> None:
        config = self.config
        if not config.repo_root.is_dir():
            raise DeployConfigError(f"ReasBook checkout does not exist: {config.repo_root}")
        if not (config.repo_root / "ReasBook" / "Books").is_dir():
            raise DeployConfigError(
                f"book catalog directory does not exist: {config.repo_root / 'ReasBook' / 'Books'}"
            )
        for name, path in (
            ("cache root", config.cache_root),
            ("reviewer data", config.data_root),
        ):
            if path == config.repo_root or config.repo_root in path.parents:
                raise DeployConfigError(f"{name} must be outside the ReasBook checkout: {path}")
        if config.stacks_root:
            for name, path in (("cache root", config.cache_root), ("reviewer data", config.data_root)):
                if path == config.stacks_root or config.stacks_root in path.parents:
                    raise DeployConfigError(f"{name} must be outside the Stacks checkout: {path}")
        if config.data_root == config.cache_root:
            raise DeployConfigError("reviewer data and cache root must be different directories")
        if not config.dry_run:
            if isinstance(self.reviewer, ReviewerAdapter) and not config.reviewer_root.is_dir():
                raise DeployConfigError(f"reviewer root does not exist: {config.reviewer_root}")
            config.data_root.mkdir(parents=True, exist_ok=True)
            config.cache_root.mkdir(parents=True, exist_ok=True)
            prepare_cache_dirs(config.cache_root)

    def selected_books(self) -> tuple[str, ...]:
        available_root = self.config.repo_root / "ReasBook" / "Books"
        available = {
            path.name.lower(): path.name
            for path in available_root.iterdir()
            if path.is_dir()
        }
        requested = self.config.books or DEFAULT_BOOKS
        selected: list[str] = []
        for value in requested:
            project = available.get(value.lower())
            if project is None or not PROJECT_ID_RE.fullmatch(project):
                raise DeployConfigError(f"unknown or unsafe book ID: {value}")
            if project in selected:
                raise DeployConfigError(f"book selected more than once: {project}")
            selected.append(project)
        return tuple(selected)

    def _commit(self, repo: Path, branch: str, *, dry_run: bool) -> str:
        if dry_run:
            return "planned"
        ref = self._git.branch_ref(repo, branch)
        return self._git.output(repo, "rev-parse", ref)

    def _book(self, project: str, branch: str) -> BookBuildResult:
        config = self.config
        started = time.monotonic()
        commit = self._commit(config.repo_root, branch, dry_run=config.dry_run)
        source = self._git.create_worktree(
            config.repo_root,
            config.cache_root,
            project,
            branch,
            dry_run=config.dry_run,
        )
        lean_root = source / "ReasBook"
        target = project
        cache_key: str | None = None
        lake = Path("lake")
        environment: dict[str, str] = {}
        if config.build or config.build_docs:
            if config.lake_bin:
                lake = Path(config.lake_bin)
            elif not config.dry_run:
                lake = ensure_toolchain(
                    lean_root,
                    runner=self.runner,
                    dry_run=False,
                    environ=os.environ,
                )
            cache_key = cache_identity(lean_root, branch, commit)
            lake_cache = config.cache_root / "lake" / cache_key
            if not config.dry_run:
                prepare_external_lake(lean_root, lake_cache)
            environment = lake_environment(
                config.cache_root, cache_key, create=not config.dry_run
            )
            if not config.dry_run:
                try:
                    from reasbook_build_sdk import library_target

                    target = library_target(lean_root, project, "book")
                except Exception as exc:
                    # Keep the public error tied to deployment rather than a
                    # package-specific exception hierarchy.
                    raise DeployExecutionError(str(exc)) from exc
            if config.build and not config.skip_cache:
                _cache_get(
                    project_root=lean_root,
                    target=project,
                    lake_bin=lake,
                    environment=environment,
                    timeout=timeout_from_env("REASBOOK_CACHE_TIMEOUT", 300.0),
                    log_path=config.cache_root / "logs" / f"{project.lower()}-cache.log",
                    runner=self.runner,
                    dry_run=config.dry_run,
                )
            if config.build:
                _build_with_sdk(
                    project_root=lean_root,
                    target=target,
                    lake_bin=lake,
                    environment=environment,
                    timeout=timeout_from_env("REASBOOK_CORE_TIMEOUT", 3600.0),
                    log_dir=config.cache_root / "logs",
                    label=f"{project.lower()}-core",
                    runner=self.runner,
                    dry_run=config.dry_run,
                )
            if config.build_docs:
                _build_with_sdk(
                    project_root=lean_root,
                    target=f"{target}:docs",
                    lake_bin=lake,
                    lake_args=("-R", "-Kenv=dev"),
                    environment=environment,
                    timeout=timeout_from_env("REASBOOK_DOCS_TIMEOUT", 3600.0),
                    log_dir=config.cache_root / "logs",
                    label=f"{project.lower()}-docs",
                    runner=self.runner,
                    dry_run=config.dry_run,
                )

        slug = project.lower()
        project_root = source / "ReasBook" / "Books" / project
        output = config.data_root / "books" / slug / "index.json"
        source_output = config.data_root / "books" / slug / "source.json"
        self._reviewer.build_index(
            ReviewIndexSpec(
                project_root=project_root,
                output=output,
                source_output=source_output,
                slug=slug,
                kind="book",
                module_prefix=project,
                branch=branch,
                commit=commit,
                source_label=f"ReasBook/{branch}/ReasBook/Books/{project}",
            ),
            dry_run=config.dry_run,
        )
        return BookBuildResult(
            slug=slug,
            project=project,
            branch=branch,
            commit=commit,
            target=target,
            source_root=str(project_root),
            index=str(output),
            source_manifest=str(source_output),
            status="planned" if config.dry_run else ("built" if config.build else "indexed"),
            elapsed_seconds=time.monotonic() - started,
            cache_key=cache_key,
        )

    def _stacks(self, stacks_root: Path) -> BookBuildResult:
        config = self.config
        started = time.monotonic()
        slug = "stacks_project"
        toolchain_file = stacks_root / "lean-toolchain"
        toolchain = toolchain_file.read_text(encoding="utf-8", errors="replace").strip() if toolchain_file.is_file() else ""
        branch = toolchain.split(":", 1)[-1] if toolchain else "v4.30.0-rc1"
        commit = self._git.output(stacks_root, "rev-parse", "HEAD", check=False) or "working-tree"
        cache_key: str | None = None
        lake = Path("lake")
        environment: dict[str, str] = {}
        if config.build_stacks:
            if config.lake_bin:
                lake = Path(config.lake_bin)
            elif not config.dry_run:
                lake = ensure_toolchain(
                    stacks_root,
                    runner=self.runner,
                    dry_run=False,
                    environ=os.environ,
                )
            dirty_digest, dirty = working_tree_fingerprint(stacks_root, runner=self.runner)
            cache_key = cache_identity(stacks_root, branch, commit)
            if dirty:
                cache_key += "-dirty-" + dirty_digest
            if not config.dry_run:
                prepare_external_lake(
                    stacks_root, config.cache_root / "lake" / f"stacks-{cache_key}"
                )
            environment = lake_environment(
                config.cache_root, cache_key, create=not config.dry_run
            )
            _build_with_sdk(
                project_root=stacks_root,
                target="stacks_project_chap04_07",
                lake_bin=lake,
                environment=environment,
                timeout=timeout_from_env("REASBOOK_STACKS_BUILD_TIMEOUT", 3600.0),
                log_dir=config.cache_root / "logs",
                label="stacks_project-core",
                runner=self.runner,
                dry_run=config.dry_run,
            )
        project_root = stacks_root / "stacks_project"
        output = config.data_root / "books" / slug / "index.json"
        source_output = config.data_root / "books" / slug / "source.json"
        self._reviewer.build_index(
            ReviewIndexSpec(
                project_root=project_root,
                output=output,
                source_output=source_output,
                slug=slug,
                kind="book",
                module_prefix="stacks_project",
                branch=branch,
                commit=commit,
                source_label="Review/stacks-proof-module-migration/stacks_project",
                max_items=config.stacks_max_items,
            ),
            dry_run=config.dry_run,
        )
        return BookBuildResult(
            slug=slug,
            project=slug,
            branch=branch,
            commit=commit,
            target="stacks_project_chap04_07",
            source_root=str(project_root),
            index=str(output),
            source_manifest=str(source_output),
            status="planned" if config.dry_run else ("built" if config.build_stacks else "indexed"),
            elapsed_seconds=time.monotonic() - started,
            cache_key=cache_key,
        )

    def deploy(self) -> DeploymentReport:
        """Run the selected-book deployment and publish one atomic manifest."""

        self.validate()
        config = self.config
        python_bin = find_python(
            requested=config.python_bin,
            workspace_root=config.repo_root.parent,
        )
        # ReviewerAdapter can be injected in tests; update the default's
        # interpreter after runtime selection.
        if self.reviewer is not None and isinstance(self.reviewer, ReviewerAdapter):
            self.reviewer.python_bin = python_bin
        selected = self.selected_books()
        results: list[BookBuildResult] = []
        with deployment_lock(config.cache_root, enabled=not config.dry_run):
            transaction_context = (
                FileTransaction(config.cache_root / "transactions")
                if not config.dry_run
                else nullcontext(None)
            )
            with transaction_context as transaction:
                for project in selected:
                    branch = self._git.choose_branch(config.repo_root, project, config.branch)
                    print(f"[deploy] selected {project} on {branch}")
                    if transaction is not None:
                        slug = project.lower()
                        transaction.watch(config.data_root / "books" / slug / "index.json")
                        transaction.watch(config.data_root / "books" / slug / "source.json")
                    results.append(self._book(project, branch))

                stacks_root = config.stacks_root
                if stacks_root and stacks_root.is_dir():
                    if transaction is not None:
                        transaction.watch(config.data_root / "books" / "stacks_project" / "index.json")
                        transaction.watch(config.data_root / "books" / "stacks_project" / "source.json")
                    results.append(self._stacks(stacks_root))
                # Optional capability stages run before catalog publication so
                # a graph/Verso/Comparator failure cannot publish a catalog
                # that advertises an incomplete deployment.
                stage_results = self.pipeline.run(dry_run=config.dry_run) if self.pipeline else ()
                if stage_results and any(not item.succeeded for item in stage_results):
                    failed = next(item for item in stage_results if not item.succeeded)
                    raise DeployExecutionError(
                        f"deployment stage {failed.name} failed: {failed.message}"
                    )
                serialized_stages = tuple(item.public_dict() for item in stage_results)
                catalog_path = config.data_root / "catalog.json"
                if transaction is not None:
                    transaction.watch(catalog_path)
                    transaction.watch(config.cache_root / "manifests" / "latest.json")
                self._reviewer.regenerate_catalog(
                    reasbook_root=config.repo_root,
                    output=catalog_path,
                    data_root=config.data_root,
                    stacks_root=stacks_root,
                    include_papers=config.include_papers,
                    dry_run=config.dry_run,
                )

                report = DeploymentReport(config, tuple(results), stages=serialized_stages)
                if not config.dry_run:
                    stamp = datetime.now(timezone.utc).strftime("%Y%m%dT%H%M%SZ")
                    manifest_path = config.cache_root / "manifests" / f"deploy-{stamp}.json"
                    transaction.watch(manifest_path)
                    report = DeploymentReport(
                        config,
                        tuple(results),
                        manifest_path,
                        serialized_stages,
                    )
                    manifest = {
                        "schemaVersion": 1,
                        "generatedAt": utc_now(),
                        **report.public_dict(),
                    }
                    write_json(manifest_path, manifest)
                    write_json(config.cache_root / "manifests" / "latest.json", manifest)
                    print(f"[deploy] manifest: {manifest_path}")
                else:
                    import json

                    print(json.dumps(report.public_dict(), ensure_ascii=False, indent=2))
        if config.serve:
            if config.dry_run:
                print(f"[deploy] would start reviewer at http://{config.host}:{config.port}/")
            else:
                launch_reviewer(config, python_bin)
        return report


def launch_reviewer(config: DeploymentConfig, python_bin: str) -> None:
    """Replace the current process with the reviewer's configured launcher."""

    launcher = config.reviewer_root / "start_server.sh"
    if not launcher.is_file() or not os.access(launcher, os.X_OK):
        raise DeployConfigError(f"reviewer launcher is not executable: {launcher}")
    environment = reviewer_environment(
        repo_root=config.repo_root,
        data_root=config.data_root,
        host=config.host,
        port=config.port,
        python_bin=python_bin,
        cache_root=config.cache_root,
    )
    print(f"[deploy] starting reviewer at http://{config.host}:{config.port}/")
    os.execve(str(launcher), [str(launcher)], environment)


__all__ = [
    "DEFAULT_BOOKS",
    "DeploymentService",
    "VERSION_BRANCH_RE",
    "launch_reviewer",
    "utc_now",
]
