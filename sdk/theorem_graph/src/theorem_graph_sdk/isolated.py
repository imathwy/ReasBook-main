"""Read existing compiled modules in bounded, independent Lean environments."""

from __future__ import annotations

import argparse
from concurrent.futures import ThreadPoolExecutor
from dataclasses import replace
from datetime import datetime, timezone
import json
import os
from pathlib import Path
import re
from threading import RLock
import time
from typing import Any

from reasbook_sdk_common import (
    Command,
    CommandRunner,
    CommandTimeoutError,
    atomic_write_json,
)

from .analysis import build_data, fallback_raw_declarations, merge_source_inventory
from .errors import ExtractionError
from .isolated_merge import merge_compiled_graphs
from .models import Project
from .render import copy_generic_map


RESOURCE_ROOT = Path(__file__).parent / "resources"
MODULE_NAME = re.compile(r"[A-Za-z_][A-Za-z0-9_']*(?:\.[A-Za-z_][A-Za-z0-9_']*)*\Z")


def available_modules(
    project: Project, compiled_root: Path, module_prefix: str
) -> tuple[list[str], list[str]]:
    """Inventory source-owned modules; never traverse package trees or run Lake."""
    if not MODULE_NAME.fullmatch(
        module_prefix
    ) or project.project_id not in module_prefix.split("."):
        raise ExtractionError(
            "module prefix must be a Lean module containing the project id"
        )
    compiled_root = compiled_root.resolve(strict=True)
    available, missing = [], []
    for source in sorted(project.root.rglob("*.lean")):
        if source.is_symlink() or not source.resolve().is_relative_to(
            project.root.resolve()
        ):
            continue
        suffix = ".".join(source.relative_to(project.root).with_suffix("").parts)
        module = f"{module_prefix}.{suffix}"
        if not MODULE_NAME.fullmatch(module):
            raise ExtractionError(f"unsupported Lean module filename: {source}")
        artifact = compiled_root.joinpath(*module.split(".")).with_suffix(".olean")
        usable = (
            artifact.is_file()
            and artifact.resolve().is_relative_to(compiled_root)
            and artifact.stat().st_size > 0
        )
        (available if usable else missing).append(module)
    return available, missing


def extract_available(
    project: Project,
    *,
    compiled_root: Path,
    module_prefix: str,
    search_paths: list[Path],
    lean_bin: Path,
    output: Path,
    branch: str,
    commit: str,
    repository: str,
    batch_size: int = 16,
    timeout: float = 1800,
    memory_mb: int = 4096,
    jobs: int = 1,
    memory_budget_mb: int | None = None,
) -> dict[str, Any]:
    """Publish one explicitly partial map without modifying source or .lake.

    Each failed batch is bisected down to one module, with separate logs/configs
    and outputs for every attempt. Successful raw environments are contracted
    immediately; only the resulting literature graphs are merged.
    """
    compiled_root = compiled_root.resolve(strict=True)
    source_root = project.root.resolve(strict=True)
    lean_bin = lean_bin.resolve(strict=True)
    search_paths = [path.resolve(strict=True) for path in search_paths]
    output = output.resolve()
    protected = [source_root, compiled_root, *search_paths, lean_bin.parent.parent]
    if output.exists() or any(
        output.is_relative_to(root) or root.is_relative_to(output) for root in protected
    ):
        raise ExtractionError(
            "output must be a new directory disjoint from source, toolchain, and compiled search paths"
        )
    if (
        not 1 <= batch_size <= 128
        or timeout <= 0
        or memory_mb <= 0
        or not branch
        or not commit
    ):
        raise ExtractionError(
            "require batch size 1..128, positive limits, branch and immutable commit"
        )
    if not 1 <= jobs <= 32 or (
        jobs > 1 and (memory_budget_mb is None or jobs * memory_mb > memory_budget_mb)
    ):
        raise ExtractionError(
            "parallel jobs require an explicit memory budget >= jobs * memory_mb (jobs 1..32)"
        )
    modules, missing = available_modules(project, compiled_root, module_prefix)
    if not modules:
        raise ExtractionError("no existing compiled project modules are available")
    output.mkdir(parents=True)
    started = time.monotonic()
    source_data = build_data(
        replace(project, root_module=None),
        fallback_raw_declarations(project),
        repository,
        branch,
        commit,
    )
    graphs: list[dict[str, Any]] = []
    attempts: list[dict[str, Any]] = []
    completed: list[str] = []
    failed: list[str] = []
    state_lock = RLock()

    def checkpoint() -> dict[str, Any]:
        report = {
            "schemaVersion": 1,
            "project": source_data["project"],
            "availableModules": modules,
            "missingModules": missing,
            "completedModules": completed,
            "failedModules": failed,
            "attempts": attempts,
            "leanThreads": 1,
            "leanMemoryLimitMb": memory_mb,
            "jobs": jobs,
            "elapsedSeconds": time.monotonic() - started,
        }
        atomic_write_json(output / "progress.json", report)
        return report

    def extract(batch: list[str]) -> None:
        with state_lock:
            number = len(attempts) + 1
            directory = output / f"environment-{number:05d}"
            directory.mkdir()
            attempt: dict[str, Any] = {"modules": batch, "directory": directory.name}
            attempts.append(attempt)
            checkpoint()
        config = directory / "config.json"
        raw = directory / "raw.json"
        atomic_write_json(
            config,
            {
                "projects": [
                    {
                        "id": project.project_id,
                        "rootModule": batch[0],
                        "rootModules": batch,
                    }
                ]
            },
        )
        command = Command(
            (
                str(lean_bin),
                "-j",
                "1",
                "-M",
                str(memory_mb),
                "--run",
                str(RESOURCE_ROOT / "Extract.lean"),
                str(config),
                str(raw),
            ),
            cwd=directory,
            timeout=timeout,
            env={
                "LEAN_PATH": os.pathsep.join(
                    str(path) for path in [compiled_root, *search_paths]
                ),
                "LEAN_NUM_THREADS": "1",
                "LEAN_SYSROOT": str(lean_bin.parent.parent),
                "PATH": str(lean_bin.parent) + os.pathsep + os.environ.get("PATH", ""),
                "TMPDIR": str(directory),
            },
        )
        try:
            attempt_started = time.monotonic()
            with state_lock:
                attempt["startedAt"] = datetime.now(timezone.utc).isoformat()
            result = CommandRunner(output_file=directory / "extract.log").run(command)
            returncode = result.returncode
        except CommandTimeoutError:
            returncode = 124
        with state_lock:
            attempt["returncode"] = returncode
            attempt["finishedAt"] = datetime.now(timezone.utc).isoformat()
            attempt["elapsedSeconds"] = time.monotonic() - attempt_started
        if returncode == 0:
            try:
                payload = json.loads(raw.read_text(encoding="utf-8"))
                if (
                    not isinstance(payload, list)
                    or len(payload) != 1
                    or payload[0].get("id") != project.project_id
                ):
                    raise ValueError("raw project identity mismatch")
                declarations = payload[0]["declarations"]
                if not isinstance(declarations, list) or any(
                    not isinstance(decl, dict)
                    or not decl.get("name")
                    or any(
                        not isinstance(decl.get(field), list)
                        for field in (
                            "dependencies",
                            "statementDependencies",
                            "proofDependencies",
                        )
                    )
                    for decl in declarations
                ):
                    raise ValueError("invalid typed declaration list")
                graph = build_data(
                    replace(project, root_module=batch[0]),
                    declarations,
                    repository,
                    branch,
                    commit,
                )
            except (OSError, ValueError, KeyError, TypeError) as exc:
                raise ExtractionError(
                    f"invalid isolated extractor result: {raw}: {exc}"
                ) from exc
            atomic_write_json(directory / "contracted.json", graph)
            with state_lock:
                graphs.append(graph)
                completed.extend(batch)
        elif len(batch) > 1:
            midpoint = len(batch) // 2
            extract(batch[:midpoint])
            extract(batch[midpoint:])
        else:
            with state_lock:
                failed.extend(batch)
        with state_lock:
            checkpoint()

    batches = [
        modules[offset : offset + batch_size]
        for offset in range(0, len(modules), batch_size)
    ]
    with ThreadPoolExecutor(max_workers=jobs) as executor:
        for _ in executor.map(extract, batches):
            pass
    if not graphs:
        raise ExtractionError(
            f"all isolated environments failed; see {output / 'progress.json'}"
        )
    graphs.sort(
        key=lambda graph: str(graph.get("generation", {}).get("rootModule", ""))
    )
    completed.sort()
    failed.sort()
    merged = merge_source_inventory(
        merge_compiled_graphs(graphs, source_data), source_data
    )
    merged["generation"].update(
        {
            "mode": "lean-environment-partial",
            "dependencyCoverage": "partial",
            "partialReason": "available-compiled-modules-with-isolated-environments",
            "availableCompiledModuleCount": len(modules),
            "sourceLeanFileCount": len(modules) + len(missing),
            "extractedModuleCount": len(completed),
            "failedModuleCount": len(failed),
        }
    )
    copy_generic_map(RESOURCE_ROOT / "assets", output / "map", merged)
    report = checkpoint()
    report["map"] = str(output / "map")
    report["status"] = "partial"
    atomic_write_json(output / "result.json", report)
    return report


def main(argv: list[str]) -> int:
    parser = argparse.ArgumentParser(prog="theorem-graph isolated", description=__doc__)
    parser.add_argument("--project-root", type=Path, required=True)
    parser.add_argument("--project-id", required=True)
    parser.add_argument("--kind", choices=("books", "papers"), default="books")
    parser.add_argument("--compiled-root", type=Path, required=True)
    parser.add_argument("--module-prefix", required=True)
    parser.add_argument("--search-path", type=Path, action="append", default=[])
    parser.add_argument("--lean-bin", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--branch", required=True)
    parser.add_argument("--commit", required=True)
    parser.add_argument("--repository", default="https://github.com/optpku/ReasBook")
    parser.add_argument("--batch-size", type=int, default=16)
    parser.add_argument("--timeout", type=float, default=1800)
    parser.add_argument("--memory-mb", type=int, default=4096)
    parser.add_argument("--jobs", type=int, default=1)
    parser.add_argument("--memory-budget-mb", type=int)
    parser.add_argument(
        "--plan",
        action="store_true",
        help="list available/missing modules without starting Lean or writing files",
    )
    args = parser.parse_args(argv)
    project = Project(
        args.kind,
        args.kind.title(),
        "Book" if args.kind == "books" else "Paper",
        args.project_id,
        args.project_root.resolve(),
    )
    if args.plan:
        modules, missing = available_modules(
            project, args.compiled_root, args.module_prefix
        )
        report = {"availableModules": modules, "missingModules": missing}
    else:
        report = extract_available(
            project,
            compiled_root=args.compiled_root,
            module_prefix=args.module_prefix,
            search_paths=args.search_path,
            lean_bin=args.lean_bin,
            output=args.output,
            branch=args.branch,
            commit=args.commit,
            repository=args.repository,
            batch_size=args.batch_size,
            timeout=args.timeout,
            memory_mb=args.memory_mb,
            jobs=args.jobs,
            memory_budget_mb=args.memory_budget_mb,
        )
    print(json.dumps(report, indent=2))
    return 0
