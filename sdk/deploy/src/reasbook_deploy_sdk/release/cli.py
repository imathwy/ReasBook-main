"""Command-line adapter for static-site release use cases."""

from __future__ import annotations

import argparse
from contextlib import contextmanager
import json
import math
import os
from pathlib import Path
import signal
import sys
import threading

from reasbook_sdk_common import atomic_write_json

from ..errors import DeployConfigError, DeployExecutionError
from ..runtime import default_cache_root
from .artifacts import artifact_policy_digest
from .build_plan import ReleaseBuildOptions
from .bundle import BundleVerifier, normalize_sha256, site_tree_digest
from .config import load_profile
from .pages_config import (
    DEFAULT_IMMUTABLE_CONVERGENCE_POLL_SECONDS,
    DEFAULT_IMMUTABLE_CONVERGENCE_TIMEOUT_SECONDS,
    GitHubPagesConfigurator,
    _validate_immutable_convergence,
)
from .service import ReleaseDeploymentResult, StaticReleaseService
from .self_hosted import SelfHostedInstaller
from .store import ReleaseStore


def _profile_path(repo_root: Path, value: str) -> Path:
    candidate = Path(value).expanduser()
    if candidate.suffix or "/" in value:
        return candidate if candidate.is_absolute() else repo_root / candidate
    return repo_root / "config" / "deploy" / f"{value}.yml"


def _sha256_argument(value: str) -> str:
    try:
        normalized = normalize_sha256(value)
    except DeployConfigError as exc:
        raise argparse.ArgumentTypeError(str(exc)) from exc
    assert normalized is not None
    return normalized


def _positive_integer(value: str) -> int:
    try:
        parsed = int(value)
    except ValueError as exc:
        raise argparse.ArgumentTypeError("expected a positive integer") from exc
    if parsed < 1:
        raise argparse.ArgumentTypeError("expected a positive integer")
    return parsed


def _positive_finite_seconds(value: str) -> float:
    try:
        parsed = float(value)
    except ValueError as exc:
        raise argparse.ArgumentTypeError(
            "expected a positive finite number of seconds"
        ) from exc
    if not math.isfinite(parsed) or parsed <= 0:
        raise argparse.ArgumentTypeError("expected a positive finite number of seconds")
    return parsed


class _ReleaseArgumentParser(argparse.ArgumentParser):
    """Apply target-dependent invariants after argparse resolves subcommands."""

    def parse_args(self, args=None, namespace=None):
        parsed = super().parse_args(args, namespace)
        command = getattr(parsed, "release_command", None)
        if command == "configure-pages":
            try:
                _validate_immutable_convergence(
                    parsed.immutable_convergence_timeout_seconds,
                    parsed.immutable_convergence_poll_seconds,
                )
            except DeployExecutionError as exc:
                self.error(str(exc))
        if (
            command in {"publish", "rollback"}
            and getattr(parsed, "target", None) == "self-hosted"
            and not (
                getattr(parsed, "health_url", None)
                or getattr(parsed, "filesystem_health_only", False)
            )
        ):
            self.error(
                "--target self-hosted requires exactly one of --health-url or "
                "--filesystem-health-only"
            )
        return parsed


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
    parser.add_argument(
        "--pages-health-timeout-seconds",
        type=float,
        default=300.0,
        help="public Pages ReleaseSpec convergence timeout after Actions succeeds",
    )


def _add_health_options(
    parser: argparse.ArgumentParser,
    *,
    required: bool,
    required_for_self_hosted: bool = False,
) -> None:
    health = parser.add_mutually_exclusive_group(required=required)
    conditional = (
        " Required when --target self-hosted." if required_for_self_hosted else ""
    )
    health.add_argument(
        "--health-url",
        help="HTTP(S) ReleaseSpec endpoint used after activation." + conditional,
    )
    health.add_argument(
        "--filesystem-health-only",
        action="store_true",
        help=(
            "explicitly validate files without probing the HTTP server." + conditional
        ),
    )


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
    parser = _ReleaseArgumentParser(
        prog="reasbook-deploy release",
        description="Plan, build, package, and publish immutable static releases.",
    )
    parser.add_argument("--repo-root", type=Path, default=Path.cwd())
    parser.add_argument("--cache-root", type=Path, default=default_cache_root())
    commands = parser.add_subparsers(dest="release_command", required=True)

    configure_pages = commands.add_parser(
        "configure-pages",
        help="configure and audit the GitHub Pages deployment boundary",
    )
    configure_pages.add_argument("--profile", default="github-pages")
    configure_pages.add_argument("--dry-run", action="store_true")
    configure_pages.add_argument(
        "--remove-policy-id",
        type=_positive_integer,
        help="remove this one numeric deployment-policy ID after exact checks",
    )
    configure_pages.add_argument(
        "--expected-policy-name",
        help="exact current name required for --remove-policy-id",
    )
    configure_pages.add_argument(
        "--expected-policy-type",
        choices=("branch", "tag"),
        help="exact current type required for --remove-policy-id",
    )
    configure_pages.add_argument(
        "--immutable-convergence-timeout-seconds",
        type=_positive_finite_seconds,
        default=DEFAULT_IMMUTABLE_CONVERGENCE_TIMEOUT_SECONDS,
        help=(
            "deadline for the immutable-releases setting to converge after an "
            "enable request (default: 300)"
        ),
    )
    configure_pages.add_argument(
        "--immutable-convergence-poll-seconds",
        type=_positive_finite_seconds,
        default=DEFAULT_IMMUTABLE_CONVERGENCE_POLL_SECONDS,
        help=(
            "GitHub polling interval while immutable releases converge "
            "(default: 5; minimum: 1)"
        ),
    )

    policy_digest = commands.add_parser(
        "policy-digest",
        help="print the trusted artifact-policy digest for a deployment profile",
    )
    policy_digest.add_argument("--profile", default="github-pages")

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
    _add_health_options(
        publish,
        required=False,
        required_for_self_hosted=True,
    )

    preview = commands.add_parser(
        "preview", help="serve an exact packaged artifact locally"
    )
    preview.add_argument("release_id")
    preview.add_argument("--artifact", choices=("pages", "full"), default="pages")
    preview.add_argument("--host", default="127.0.0.1")
    preview.add_argument("--port", type=int, default=18000)
    preview.add_argument("--public-prefix", default="")
    preview.add_argument("--dry-run", action="store_true")

    validate = commands.add_parser(
        "validate",
        help="verify and exercise both packaged artifacts locally",
    )
    validate.add_argument("release_id")
    validate.add_argument(
        "--browser-mode",
        choices=("auto", "required", "skip"),
        default="auto",
        help=(
            "run Playwright when available (auto), require it for a release "
            "gate, or explicitly skip it"
        ),
    )
    validate.add_argument(
        "--keep-workdir",
        action="store_true",
        help="retain extracted validation trees after a successful run",
    )

    deploy = commands.add_parser("deploy", help="run the complete release flow")
    deploy.add_argument("--profile", default="github-pages")
    deploy.add_argument("--only", action="append", default=[])
    _add_build_options(deploy)
    deploy.add_argument("--no-publish", action="store_true")
    _add_publish_options(deploy)
    deploy.add_argument("--dry-run", action="store_true")
    deploy.add_argument("--new-release", action="store_true")
    deploy.add_argument("--no-fetch", action="store_true")
    deploy.add_argument(
        "--allow-local-all-active-build",
        action="store_true",
        help="explicitly permit the local builder to build every active project",
    )

    status = commands.add_parser("status", help="show persisted release state")
    status.add_argument("release_id")

    verify = commands.add_parser(
        "verify", help="verify and optionally extract a bundle"
    )
    verify.add_argument("bundle", type=Path)
    verify.add_argument("--sha256", type=_sha256_argument)
    verify.add_argument("--extract-to", type=Path)
    verify.add_argument(
        "--profile",
        help="load all verifier limits from this trusted deployment profile",
    )
    verify.add_argument(
        "--artifact-policy",
        choices=("full", "pages"),
        help="artifact policy to load with --profile",
    )
    verify.add_argument("--max-site-files", type=_positive_integer)
    verify.add_argument(
        "--max-site-bytes",
        type=_positive_integer,
    )
    verify.add_argument(
        "--max-archive-members",
        type=_positive_integer,
    )

    install = commands.add_parser(
        "install", help="atomically install a full bundle on a static server"
    )
    install.add_argument("bundle", type=Path)
    install.add_argument(
        "--expected-bundle-sha256",
        required=True,
        type=_sha256_argument,
        help=(
            "trusted full-bundle SHA-256 obtained independently of the "
            "transferred bundle and ReleaseSet"
        ),
    )
    install.add_argument("--release-set", type=Path, required=True)
    install.add_argument(
        "--artifact-policy-sha256",
        required=True,
        type=_sha256_argument,
        help="trusted expected ReleaseSet policy digest",
    )
    install.add_argument("--deploy-root", type=Path, required=True)
    _add_health_options(install, required=True)

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
    _add_health_options(
        rollback,
        required=False,
        required_for_self_hosted=True,
    )
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
    if command == "policy-digest":
        profile_path = _profile_path(Path(args.repo_root), args.profile)
        profile = load_profile(profile_path, repo_root=Path(args.repo_root))
        _print(artifact_policy_digest(profile.artifacts), as_json=False)
        return 0
    if command == "configure-pages":
        profile_path = _profile_path(Path(args.repo_root), args.profile)
        profile = load_profile(profile_path, repo_root=Path(args.repo_root))
        _print(
            GitHubPagesConfigurator(
                profile.publish,
                repo_root=Path(args.repo_root),
            ).configure(
                dry_run=args.dry_run,
                remove_policy_id=args.remove_policy_id,
                expected_policy_name=args.expected_policy_name,
                expected_policy_type=args.expected_policy_type,
                immutable_convergence_timeout_seconds=(
                    args.immutable_convergence_timeout_seconds
                ),
                immutable_convergence_poll_seconds=(
                    args.immutable_convergence_poll_seconds
                ),
            )
        )
        return 0
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
            pages_health_timeout_seconds=args.pages_health_timeout_seconds,
            dry_run=args.dry_run,
            reuse=not args.new_release,
            fetch=not args.no_fetch,
            allow_local_all_active=args.allow_local_all_active_build,
        )
        _print(result)
        return 0
    if command == "verify":
        policy_options = (args.profile, args.artifact_policy)
        manual_limits = (
            args.max_site_files,
            args.max_site_bytes,
            args.max_archive_members,
        )
        if any(policy_options) and not all(policy_options):
            raise SystemExit("--profile and --artifact-policy must be used together")
        if all(policy_options):
            if any(value is not None for value in manual_limits):
                raise SystemExit(
                    "profile-backed verification cannot override artifact limits"
                )
            profile_path = _profile_path(Path(args.repo_root), args.profile)
            profile = load_profile(profile_path, repo_root=Path(args.repo_root))
            verifier = BundleVerifier.for_policy(profile.artifact(args.artifact_policy))
        else:
            limits = {
                "max_site_files": args.max_site_files,
                "max_site_bytes": args.max_site_bytes,
                "max_archive_members": args.max_archive_members,
            }
            verifier = BundleVerifier(
                **{name: value for name, value in limits.items() if value is not None}
            )
        manifest = verifier.verify(
            args.bundle,
            expected_sha256=args.sha256,
            extract_to=args.extract_to,
        )
        if args.artifact_policy and manifest.artifact != args.artifact_policy:
            raise DeployExecutionError(
                "verified bundle artifact does not match the selected policy"
            )
        _print(manifest)
        return 0
    if command == "install":
        _print(
            SelfHostedInstaller(args.deploy_root).install(
                args.bundle,
                release_set=args.release_set,
                expected_sha256=args.expected_bundle_sha256,
                expected_artifact_policy_sha256=(args.artifact_policy_sha256),
                artifact="full",
                health_url=args.health_url,
                filesystem_health_only=args.filesystem_health_only,
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
                filesystem_health_only=args.filesystem_health_only,
            )
        )
        return 0

    context = service.context(args.release_id)
    if command == "validate":
        _print(
            service.validate(
                context,
                browser_mode=args.browser_mode,
                keep_workdir=args.keep_workdir,
            )
        )
        return 0
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
            raise SystemExit(f"{args.artifact} artifact site is not packaged: {site}")
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
        script = Path(args.repo_root).resolve() / "scripts" / "preview" / "serve.py"
        url = (
            f"http://{args.host}:{args.port}"
            f"{args.public_prefix}{context.spec.base_path}"
        )
        if args.dry_run:
            _print(
                {
                    "artifact": args.artifact,
                    "routing_mode": "strict",
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
                "--routing-mode",
                "strict",
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
        acceptance = service.require_acceptance(context)
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
        try:
            accepted_full_sha256 = str(acceptance["artifacts"]["full"]["bundle_sha256"])
        except (KeyError, TypeError) as exc:
            raise DeployExecutionError(
                "release acceptance evidence has no full-bundle identity"
            ) from exc
        if bundle.bundle_sha256 != accepted_full_sha256:
            raise DeployExecutionError(
                "full bundle metadata changed after release acceptance"
            )
        _print(
            SelfHostedInstaller(args.deploy_root).install(
                Path(bundle.bundle),
                release_set=context.layout.release_set,
                expected_sha256=accepted_full_sha256,
                expected_artifact_policy_sha256=artifact_policy_digest(
                    context.profile.artifacts
                ),
                artifact="full",
                health_url=args.health_url,
                filesystem_health_only=args.filesystem_health_only,
            )
        )
        return 0
    if command in {"publish", "rollback"}:
        _print(
            service.publish(
                context,
                wait=args.wait,
                wait_timeout_seconds=args.wait_timeout_seconds,
                pages_health_timeout_seconds=args.pages_health_timeout_seconds,
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
            else service.promote(
                context,
                wait=args.wait,
                wait_timeout_seconds=args.wait_timeout_seconds,
                pages_health_timeout_seconds=args.pages_health_timeout_seconds,
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
