"""Command-line entry points for the ReasBook deployment SDK."""

from __future__ import annotations

import argparse
import os
from pathlib import Path
import re
import subprocess
import sys

from .ci import (
    compress_cache,
    decompress_cache,
    heartbeat,
    install_elan,
    prepare_cache,
    retry_on_143,
    verify_python,
)
from .docker import DockerDeploymentConfig, deploy_static
from .errors import DeployError
from .models import DeploymentConfig
from .runtime import (
    default_cache_root,
    prepare_project_runtime,
    read_env_defaults,
    resolve_path,
    timeout_from_env,
)
from .service import DeploymentService


CI_COMMANDS = {
    "verify-python",
    "install-elan",
    "prepare-cache",
    "heartbeat",
    "retry-143",
    "compress-cache",
    "decompress-cache",
}


def _runtime_main(argv: list[str]) -> int:
    parser = argparse.ArgumentParser(
        prog="reasbook-deploy runtime",
        description="Prepare a Lake runtime and execute one argv command.",
    )
    parser.add_argument("project", type=Path)
    parser.add_argument("--cache-root", type=Path, default=default_cache_root())
    parser.add_argument("--cache-prefix", default="")
    parser.add_argument("--cwd", type=Path)
    parser.add_argument("--no-link-lake", action="store_true")
    parser.add_argument("--force-external-lake", action="store_true")
    parser.add_argument("--dry-run", action="store_true")
    if "--" not in argv:
        if any(value in {"-h", "--help"} for value in argv):
            parser.parse_args(argv)
        raise DeployError(
            "usage: reasbook-deploy runtime [OPTIONS] PROJECT -- COMMAND [ARGS...]"
        )
    separator = argv.index("--")
    option_values = argv[:separator]
    command = argv[separator + 1 :]
    if not command:
        raise DeployError("runtime requires a command after --")
    args = parser.parse_args(option_values)
    runtime_env = prepare_project_runtime(
        args.project,
        cache_root=args.cache_root,
        cache_prefix=args.cache_prefix,
        link_external_lake=not args.no_link_lake,
        force_external_lake=args.force_external_lake,
        dry_run=args.dry_run,
    )
    cwd = resolve_path(args.cwd) if args.cwd else Path.cwd()
    if args.dry_run:
        print(f"[runtime] would run in {cwd}: {command!r}")
        return 0
    result = subprocess.run(command, cwd=cwd, env={**os.environ, **runtime_env})
    return 128 + (-result.returncode) if result.returncode < 0 else result.returncode


def _docker_main(argv: list[str]) -> int:
    parser = argparse.ArgumentParser(
        prog="reasbook-deploy docker",
        description="Build and publish the static ReasBook site with Compose.",
    )
    parser.add_argument("--repo-root", type=Path, default=_repo_root())
    parser.add_argument("--compose-file", type=Path)
    parser.add_argument("--site-root", type=Path)
    parser.add_argument("--cache-root", type=Path, default=default_cache_root())
    parser.add_argument("--port", type=int, default=int(os.environ.get("REASBOOK_PORT", "3200")))
    parser.add_argument("--skip-build", action="store_true")
    parser.add_argument("--dry-run", action="store_true")
    args = parser.parse_args(argv)
    root = _repo_root(args.repo_root)
    compose = args.compose_file or root / "docker-compose.yml"
    site = args.site_root or root / "ReasBookWeb" / "_site"
    deploy_static(
        DockerDeploymentConfig(
            repo_root=root,
            compose_file=compose,
            site_root=site,
            cache_root=args.cache_root,
            port=args.port,
            skip_build=args.skip_build,
            dry_run=args.dry_run,
        )
    )
    return 0


def _repo_root(value: str | Path | None = None) -> Path:
    candidate = Path(value).expanduser() if value else Path.cwd()
    candidate = candidate.resolve()
    if (candidate / "ReasBook" / "lakefile.lean").is_file():
        return candidate
    if (candidate / "ReasBook" / "ReasBook" / "lakefile.lean").is_file():
        return candidate / "ReasBook"
    # Accept the Lean subdirectory as a convenience, but normalize it back to
    # the repository root expected by branch/catalog discovery.
    if (candidate / "lakefile.lean").is_file() and (candidate / "Books").is_dir():
        return candidate.parent
    return candidate


def build_parser(repo_root: Path | None = None) -> argparse.ArgumentParser:
    """Build the selected-book deployment parser."""

    root = _repo_root(repo_root)
    workspace = root.parent
    parser = argparse.ArgumentParser(
        prog="reasbook-deploy",
        description="Build isolated ReasBook projects and publish reviewer indexes.",
    )
    parser.add_argument("--repo-root", type=Path, default=root)
    parser.add_argument("--book", action="append", dest="books", help="book ID or slug; repeat for at most two books")
    parser.add_argument("--branch", help="version branch applied to every selected book")
    parser.add_argument("--cache-root", type=Path, default=default_cache_root())
    parser.add_argument("--reviewer-root", type=Path, default=root / "apps" / "reasbook-reviewer")
    parser.add_argument("--reviewer-data", type=Path)
    parser.add_argument("--stacks-root", type=Path, default=workspace / "Review" / "stacks-proof-module-migration")
    parser.add_argument("--no-stacks", action="store_true")
    parser.add_argument("--include-papers", action="store_true")
    parser.add_argument("--no-build", action="store_true", help="only publish lightweight source indexes")
    parser.add_argument("--build-docs", action="store_true")
    parser.add_argument("--skip-cache", action="store_true")
    parser.add_argument("--build-stacks", action="store_true")
    parser.add_argument("--stacks-max-items", type=int, default=0)
    parser.add_argument("--dry-run", action="store_true")
    parser.add_argument("--serve", action="store_true")
    parser.add_argument("--host")
    parser.add_argument("--port", type=int)
    parser.add_argument("--lake-bin")
    return parser


def parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    return build_parser().parse_args(argv)


def _deployment_config(args: argparse.Namespace) -> DeploymentConfig:
    repo_root = _repo_root(args.repo_root)
    workspace = repo_root.parent
    reviewer_root = resolve_path(args.reviewer_root, workspace)
    reviewer_env = read_env_defaults(reviewer_root / ".env")
    host = args.host or os.environ.get("REASBOOK_REVIEWER_HOST") or reviewer_env.get("REASBOOK_REVIEWER_HOST") or "127.0.0.1"
    raw_port = args.port
    if raw_port is None:
        raw_port = os.environ.get("REASBOOK_REVIEWER_PORT") or reviewer_env.get("REASBOOK_REVIEWER_PORT") or "8876"
    try:
        port = int(raw_port)
    except (TypeError, ValueError):
        raise DeployError("REASBOOK_REVIEWER_PORT must be an integer") from None
    if args.branch and not re.fullmatch(r"v\d+\.\d+\.\d+", args.branch):
        raise DeployError("--branch must look like vX.Y.Z")
    cache_root = resolve_path(args.cache_root, workspace)
    configured_data = args.reviewer_data or os.environ.get("REASBOOK_REVIEWER_DATA") or reviewer_env.get("REASBOOK_REVIEWER_DATA")
    data_root = resolve_path(configured_data, workspace) if configured_data else cache_root / "reviewer" / "data"
    stacks_root = None if args.no_stacks else resolve_path(args.stacks_root, workspace)
    return DeploymentConfig(
        repo_root=repo_root,
        reviewer_root=reviewer_root,
        data_root=data_root,
        cache_root=cache_root,
        books=tuple(args.books or ()),
        branch=args.branch,
        stacks_root=stacks_root,
        include_papers=args.include_papers,
        build=not args.no_build,
        build_docs=args.build_docs,
        skip_cache=args.skip_cache,
        build_stacks=args.build_stacks,
        stacks_max_items=args.stacks_max_items,
        dry_run=args.dry_run,
        serve=args.serve,
        host=host,
        port=port,
        python_bin=os.environ.get("REASBOOK_PYTHON_BIN") or os.environ.get("REASBOOK_PYTHON"),
        lake_bin=args.lake_bin or os.environ.get("LAKE_BIN"),
    )


def _ci_main(argv: list[str]) -> int:
    if argv and argv[0] == "ci":
        argv = argv[1:]
    if not argv:
        raise DeployError("a CI subcommand is required")
    command, *rest = argv
    if command == "verify-python":
        verify_python()
        return 0
    if command == "install-elan":
        install_elan()
        return 0
    if command == "prepare-cache":
        if len(rest) != 1:
            raise DeployError("usage: prepare-cache BRANCH")
        prepare_cache(rest[0])
        return 0
    if command == "heartbeat":
        if len(rest) < 2:
            raise DeployError("usage: heartbeat LABEL COMMAND [ARGS...]")
        return heartbeat(rest[0], rest[1:])
    if command == "retry-143":
        if not rest:
            raise DeployError("usage: retry-143 COMMAND [ARGS...]")
        return retry_on_143(rest)
    if command == "compress-cache":
        if len(rest) != 1:
            raise DeployError("usage: compress-cache LAKE_DIR")
        compress_cache(
            rest[0],
            timeout_seconds=timeout_from_env("REASBOOK_CACHE_ARCHIVE_TIMEOUT", 1800.0),
        )
        return 0
    if command == "decompress-cache":
        if len(rest) != 1:
            raise DeployError("usage: decompress-cache LAKE_DIR")
        decompress_cache(
            rest[0],
            timeout_seconds=timeout_from_env("REASBOOK_CACHE_ARCHIVE_TIMEOUT", 1800.0),
        )
        return 0
    raise DeployError(f"unknown CI subcommand: {command}")


def main(argv: list[str] | None = None) -> int:
    values = list(sys.argv[1:] if argv is None else argv)
    try:
        if values and values[0] == "release":
            from .release.cli import main as release_main

            return release_main(values[1:])
        if values and values[0] == "docker":
            return _docker_main(values[1:])
        if values and values[0] == "runtime":
            return _runtime_main(values[1:])
        if values and (values[0] == "ci" or values[0] in CI_COMMANDS):
            return _ci_main(values)
        args = parse_args(values)
        if args.no_build and (args.build_docs or args.build_stacks):
            print(
                "[deploy] warning: --no-build disables --build-docs/--build-stacks",
                file=sys.stderr,
            )
        report = DeploymentService(_deployment_config(args)).deploy()
        if args.dry_run:
            # The service already prints the machine-readable plan; keeping
            # this return value stable lets shell wrappers compose it.
            return 0
        return 0 if all(result.error is None for result in report.results) else 1
    except (DeployError, OSError, ValueError) as exc:
        print(f"reasbook-deploy: {exc}", file=sys.stderr)
        return 2


__all__ = ["build_parser", "main", "parse_args"]
