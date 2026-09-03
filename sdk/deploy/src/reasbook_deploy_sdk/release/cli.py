"""Command-line adapter for static-site release use cases."""

from __future__ import annotations

import argparse
from contextlib import contextmanager
import json
import os
from pathlib import Path
import signal
import sys
import threading

from reasbook_sdk_common import atomic_write_json

from ..runtime import default_cache_root
from .build_plan import ReleaseBuildOptions
from .bundle import BundleVerifier, site_tree_digest
from .service import ReleaseDeploymentResult, StaticReleaseService
from .self_hosted import SelfHostedInstaller
from .store import ReleaseStore


def _profile_path(repo_root: Path, value: str) -> Path:
    candidate = Path(value).expanduser()
    if candidate.suffix or "/" in value:
        return candidate if candidate.is_absolute() else repo_root / candidate
    return repo_root / "config" / "deploy" / f"{value}.yml"


def _service(args: argparse.Namespace) -> StaticReleaseService:
    return StaticReleaseService(
        Path(args.repo_root),
        Path(args.cache_root),
    )


def _build_options(args: argparse.Namespace) -> ReleaseBuildOptions:
    return ReleaseBuildOptions(
        max_parallel_branches=args.max_parallel_branches,
        build_timeout_seconds=args.build_timeout_seconds,
        docs_timeout_seconds=args.docs_timeout_seconds,
        verso_timeout_seconds=args.verso_timeout_seconds,
        graph_timeout_seconds=args.graph_timeout_seconds,
    )


def _add_build_options(parser: argparse.ArgumentParser) -> None:
    parser.add_argument("--max-parallel-branches", type=int, default=3)
    parser.add_argument("--build-timeout-seconds", type=float, default=21600.0)
    parser.add_argument("--docs-timeout-seconds", type=float, default=43200.0)
    parser.add_argument("--verso-timeout-seconds", type=float, default=21600.0)
    parser.add_argument("--graph-timeout-seconds", type=float, default=3600.0)


def _add_publish_options(parser: argparse.ArgumentParser) -> None:
    parser.add_argument("--wait", action="store_true")
    parser.add_argument("--wait-timeout-seconds", type=float, default=1800.0)


def _print(value, *, as_json: bool = True) -> None:
    payload = value.public_dict() if hasattr(value, "public_dict") else value
    if as_json:
        print(json.dumps(payload, ensure_ascii=False, indent=2, sort_keys=True))
    else:
        print(payload)


def _status_payload(context) -> dict:
    store = ReleaseStore(context.layout)
    value = {
        "state": store.load_state().public_dict(),
        "release": context.spec.public_dict(),
        "build": None,
        "bundle": None,
        "pages_bundle": None,
        "release_set": None,
        "publication": None,
    }
    if context.layout.build_report.is_file():
        value["build"] = store.load_build_report().public_dict()
    if context.layout.bundle_info.is_file():
        value["bundle"] = store.load_bundle_info().public_dict()
    if context.layout.pages_bundle_info.is_file():
        value["pages_bundle"] = store.load_pages_bundle_info().public_dict()
    if context.layout.release_set.is_file():
        value["release_set"] = store.load_release_set().public_dict()
    if context.layout.publication.is_file():
        value["publication"] = store.load_publication().public_dict()
    return value


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(
        prog="reasbook-deploy release",
        description="Plan, build, package, and publish immutable static releases.",
    )
    parser.add_argument("--repo-root", type=Path, default=Path.cwd())
    parser.add_argument("--cache-root", type=Path, default=default_cache_root())
    commands = parser.add_subparsers(dest="release_command", required=True)

    plan = commands.add_parser("plan", help="resolve immutable release inputs")
    plan.add_argument("--profile", default="github-pages")
    plan.add_argument("--only", action="append", default=[])
    plan.add_argument("--output", type=Path)
    plan.add_argument("--new-release", action="store_true")
    plan.add_argument("--fetch", action="store_true")

    for name in ("build", "resume"):
        command = commands.add_parser(name, help=f"{name} a local release")
        command.add_argument("release_id")
        _add_build_options(command)
        if name == "build":
            command.add_argument("--dry-run", action="store_true")
        if name == "resume":
            command.add_argument("--no-publish", action="store_true")
            _add_publish_options(command)

    package = commands.add_parser(
        "package", help="package full and GitHub Pages artifacts"
    )
    package.add_argument("release_id")

    publish = commands.add_parser("publish", help="publish a packaged release")
    publish.add_argument("release_id")
    _add_publish_options(publish)
    publish.add_argument("--dry-run", action="store_true")
    publish.add_argument(
        "--target",
        choices=("github-pages", "self-hosted"),
        default="github-pages",
    )
    publish.add_argument("--deploy-root", type=Path)
    publish.add_argument("--health-url")

    preview = commands.add_parser(
        "preview", help="serve an exact packaged artifact locally"
    )
    preview.add_argument("release_id")
    preview.add_argument("--artifact", choices=("pages", "full"), default="pages")
    preview.add_argument("--host", default="127.0.0.1")
    preview.add_argument("--port", type=int, default=18000)
    preview.add_argument("--public-prefix", default="")
    preview.add_argument("--dry-run", action="store_true")

    deploy = commands.add_parser("deploy", help="run the complete release flow")
    deploy.add_argument("--profile", default="github-pages")
    deploy.add_argument("--only", action="append", default=[])
    _add_build_options(deploy)
    deploy.add_argument("--no-publish", action="store_true")
    _add_publish_options(deploy)
    deploy.add_argument("--dry-run", action="store_true")
    deploy.add_argument("--new-release", action="store_true")
    deploy.add_argument("--no-fetch", action="store_true")

    status = commands.add_parser("status", help="show persisted release state")
    status.add_argument("release_id")

    verify = commands.add_parser(
        "verify", help="verify and optionally extract a bundle"
    )
    verify.add_argument("bundle", type=Path)
    verify.add_argument("--sha256")
    verify.add_argument("--extract-to", type=Path)

    install = commands.add_parser(
        "install", help="atomically install a full bundle on a static server"
    )
    install.add_argument("bundle", type=Path)
    install.add_argument("--sha256", required=True)
    install.add_argument("--deploy-root", type=Path, required=True)
    install.add_argument("--health-url")

    rollback = commands.add_parser(
        "rollback", help="republish a previous immutable release"
    )
    rollback.add_argument("--to", dest="release_id", required=True)
    _add_publish_options(rollback)
    rollback.add_argument("--dry-run", action="store_true")
    rollback.add_argument(
        "--target",
        choices=("github-pages", "self-hosted"),
        default="github-pages",
    )
    rollback.add_argument("--deploy-root", type=Path)
    rollback.add_argument("--health-url")
    return parser


@contextmanager
def _release_signals():
    if threading.current_thread() is not threading.main_thread():
        yield
        return
    previous = {
        signum: signal.getsignal(signum) for signum in (signal.SIGINT, signal.SIGTERM)
    }

    def stop(signum, _frame):
        raise SystemExit(128 + signum)

    for signum in previous:
        signal.signal(signum, stop)
    try:
        yield
    finally:
        for signum, handler in previous.items():
            signal.signal(signum, handler)


def main(argv: list[str] | None = None) -> int:
    with _release_signals():
        return _main(argv)


def _main(argv: list[str] | None = None) -> int:
    args = build_parser().parse_args(argv)
    service = _service(args)
    command = args.release_command
    if command == "plan":
        profile = _profile_path(Path(args.repo_root), args.profile)
        context = service.plan(
            profile,
            only=args.only,
            reuse=not args.new_release,
            fetch=args.fetch,
        )
        if args.output:
            output = Path(args.output).expanduser()
            if not output.is_absolute():
                output = Path.cwd() / output
            atomic_write_json(output.resolve(strict=False), context.spec.public_dict())
        _print(context.spec)
        return 0
    if command == "deploy":
        profile = _profile_path(Path(args.repo_root), args.profile)
        result = service.deploy(
            profile,
            only=args.only,
            options=_build_options(args),
            publish=not args.no_publish,
            wait=args.wait,
            wait_timeout_seconds=args.wait_timeout_seconds,
            dry_run=args.dry_run,
            reuse=not args.new_release,
            fetch=not args.no_fetch,
        )
        _print(result)
        return 0
    if command == "verify":
        manifest = BundleVerifier().verify(
            args.bundle,
            expected_sha256=args.sha256,
            extract_to=args.extract_to,
        )
        _print(manifest)
        return 0
    if command == "install":
        _print(
            SelfHostedInstaller(args.deploy_root).install(
                args.bundle,
                expected_sha256=args.sha256,
                artifact="full",
                health_url=args.health_url,
            )
        )
        return 0

    if command == "rollback" and args.target == "self-hosted":
        if args.deploy_root is None:
            raise SystemExit("--deploy-root is required for self-hosted rollback")
        if args.dry_run:
            _print(
                {
                    "status": "planned",
                    "target": "self-hosted",
                    "release_id": args.release_id,
                    "deployment_root": str(args.deploy_root.expanduser()),
                }
            )
            return 0
        _print(
            SelfHostedInstaller(args.deploy_root).rollback(
                args.release_id,
                health_url=args.health_url,
            )
        )
        return 0

    context = service.context(args.release_id)
    if command == "preview":
        store = ReleaseStore(context.layout)
        site = (
            context.layout.pages_site
            if args.artifact == "pages"
            else context.layout.site
        )
        bundle = (
            store.load_pages_bundle_info()
            if args.artifact == "pages"
            else store.load_bundle_info()
        )
        if not (site / "index.html").is_file():
            raise SystemExit(
                f"{args.artifact} artifact site is not packaged: {site}"
            )
        manifest = BundleVerifier().inspect(
            Path(bundle.bundle),
            expected_sha256=bundle.bundle_sha256,
        )
        digest, file_count, total_bytes = site_tree_digest(site)
        if (
            manifest.artifact != args.artifact
            or digest != manifest.site_tree_sha256
            or file_count != manifest.file_count
            or total_bytes != manifest.total_bytes
        ):
            raise SystemExit(
                f"{args.artifact} preview tree differs from its packaged bundle"
            )
        script = (
            Path(args.repo_root).resolve()
            / "scripts"
            / "preview"
            / "serve.py"
        )
        url = (
            f"http://{args.host}:{args.port}"
            f"{args.public_prefix}{context.spec.base_path}"
        )
        if args.dry_run:
            _print(
                {
                    "artifact": args.artifact,
                    "site": str(site),
                    "url": url,
                }
            )
            return 0
        environment = dict(os.environ)
        environment.update(
            {
                "REASBOOK_SITE_DIR": str(site),
                "REASBOOK_DOC_SOURCE": str(site / "docs"),
                "REASBOOK_SITE_ROOT": context.spec.base_path,
            }
        )
        os.execve(
            sys.executable,
            [
                sys.executable,
                str(script),
                str(args.port),
                "--host",
                args.host,
                "--site-root",
                context.spec.base_path,
                "--public-prefix",
                args.public_prefix,
            ],
            environment,
        )
    if command == "build":
        if args.dry_run:
            from .builder import LocalReleaseBuilder

            builder = LocalReleaseBuilder(
                Path(args.repo_root),
                Path(args.repo_root),
                Path(args.cache_root),
                context.layout,
                options=_build_options(args),
            )
            _print(
                {
                    "release_id": context.spec.release_id,
                    "branches": [
                        plan.public_dict()
                        for plan in builder.plan(
                            context.spec,
                            prepare_worktrees=False,
                        )
                    ],
                }
            )
            return 0
        _print(service.build(context, options=_build_options(args)))
        return 0
    if command == "package":
        _print(service.package(context))
        return 0
    if command == "publish" and args.target == "self-hosted":
        if args.deploy_root is None:
            raise SystemExit("--deploy-root is required for self-hosted publish")
        store = ReleaseStore(context.layout)
        state = store.load_state()
        if "package" not in state.completed:
            raise SystemExit("release artifacts have not been packaged")
        bundle = store.load_bundle_info()
        if args.dry_run:
            _print(
                {
                    "status": "planned",
                    "target": "self-hosted",
                    "release_id": context.spec.release_id,
                    "bundle": bundle.bundle,
                    "deployment_root": str(args.deploy_root.expanduser()),
                }
            )
            return 0
        _print(
            SelfHostedInstaller(args.deploy_root).install(
                Path(bundle.bundle),
                expected_sha256=bundle.bundle_sha256,
                artifact="full",
                health_url=args.health_url,
            )
        )
        return 0
    if command in {"publish", "rollback"}:
        _print(
            service.publish(
                context,
                wait=args.wait,
                wait_timeout_seconds=args.wait_timeout_seconds,
                dry_run=args.dry_run,
                force=command == "rollback",
            )
        )
        return 0
    if command == "resume":
        state = ReleaseStore(context.layout).load_state()
        if state.status == "published" and not args.no_publish:
            _print(state)
            return 0
        report = service.build(context, options=_build_options(args))
        package = service.package(context)
        publication = (
            None
            if args.no_publish
            else service.publish(
                context,
                wait=args.wait,
                wait_timeout_seconds=args.wait_timeout_seconds,
            )
        )
        refreshed = service.context(context.spec.release_id)
        _print(
            ReleaseDeploymentResult(
                refreshed,
                report,
                package,
                publication,
            )
        )
        return 0
    if command == "status":
        _print(_status_payload(context))
        return 0
    raise AssertionError(f"unhandled release command: {command}")


__all__ = ["build_parser", "main"]
