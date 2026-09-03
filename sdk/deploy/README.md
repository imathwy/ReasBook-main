# ReasBook Deploy SDK

`reasbook-deploy-sdk` is the orchestration layer for ReasBook deployments. It
coordinates the capability SDKs and repository-specific reviewer adapters:

```text
common -> build / verso / theorem_graph / comparator
                 \          |          /
                       deploy
```

The deploy package owns policy and sequencing only:

- select a stable version branch and create a detached sparse worktree;
- keep Lake, Mathlib, XDG, logs, and manifests under one external cache root;
- call the build SDK for Lean targets and the reviewer adapter for lightweight
  per-book indexes;
- publish the reviewer catalog and an atomic deployment manifest;
- expose the small CI runtime helpers as subcommands.

It does not edit Lean source files and it does not import reviewer application
internals. Expensive documentation, Verso, theorem-graph, and Comparator work
are represented by the `VersoStage`, `TheoremGraphStage`, and
`ComparatorStage` adapters (with `CallableStage` for build/publish policies).
Add them to a `DeploymentPipeline` when a deployment needs those stages; the
default local review deployment intentionally leaves them off.

## Install

Install the shared package and capability packages before this package:

```bash
python3.11 -m pip install -e sdk/common
python3.11 -m pip install -e sdk/build -e sdk/verso \
  -e sdk/theorem_graph -e sdk/comparator -e sdk/deploy
```

The deploy distribution declares those five sibling SDKs as required runtime
dependencies. For a transferred wheel installation, place all six SDK wheels
in one directory, make a compatible PyYAML wheel or package index available,
and pass the SDK directory to pip with `--find-links`.

The repository's `sdk/deploy/bin/reasbook-deploy` entry point sets local source
paths automatically, so an editable install is not required for a checkout.

## Project runtime

Repository build adapters execute capability CLIs through one runtime boundary:

```bash
./sdk/deploy/bin/reasbook-deploy runtime ReasBook -- \
  ./sdk/build/bin/reasbook-build build ReasBook --lake-arg=-R
```

The runtime command selects Python 3.11+, ensures the pinned Elan toolchain,
links `.lake` to the fixed external cache, and supplies Lake, Mathlib, XDG,
build-SDK, and Verso environment values to the child process. Use
`--cache-prefix web-` for a separate web cache or `--no-link-lake` when a
caller intentionally manages `.lake` itself.

## Static releases

The static-site release bounded context is documented in
[`release/README.md`](src/reasbook_deploy_sdk/release/README.md). It adds
immutable cross-branch planning, explicit canonical versions, target-specific
`full` and `pages` artifacts, a binding ReleaseSet, and atomic self-hosted or
GitHub Pages publication without mixing those concerns into reviewer
deployment.

The publisher reads existing releases through GitHub's raw REST API. Only an
explicit HTTP 404 is treated as a missing release; all other lookup errors and
incomplete asset metadata fail closed.

## Selected-book deployment

Run from the ReasBook checkout (or pass `--repo-root`):

```bash
./sdk/deploy/bin/reasbook-deploy \
  --book IntroductiontoRealAnalysisVolumeI_JiriLebl_2025 \
  --no-build --serve
```

The first run should use `--no-build`. It creates only source indexes and a
catalog. A real Lean build is opt-in:

```bash
./sdk/deploy/bin/reasbook-deploy --book Analysis2_Tao_2022
```

At most two books are selected per local run. Stacks is included in the
catalog when its sibling checkout exists; its Lean build is opt-in with
`--build-stacks`.

All generated build state is outside the source checkout by default:

```text
/volume/math/users/zcwang/ReasBook_Reviewer/cache/reasbook/
  sources/   detached sparse worktrees
  lake/      branch/toolchain-specific Lake trees
  toolchains/ pinned Lean/Elan toolchains shared by workers
  mathlib/   Mathlib native cache
  xdg/       package-manager cache
  e2e/       per-task source, build, graph, and task logs
  logs/      command output
  locks/     cache and publication locks
  manifests/ atomic deployment records
  ci/        CI branch cache state (unless PERSIST_ROOT is supplied)
```

Build cache directories are keyed by branch, source revision, toolchain, and
Lake manifest digest (dirty Stacks worktrees also include a content
fingerprint). Index/source/catalog publication is transactional: a failed
second project restores the files from before the run.

Use `--cache-root` and `--reviewer-data` to select different volumes. The SDK
defaults to `/volume/math/users/zcwang/ReasBook_Reviewer/cache/reasbook`,
rejects roots inside the ReasBook checkout, and refuses to reuse an unmarked
source directory. Set `REASBOOK_CACHE_ROOT` or pass `--cache-root` when
running on another machine or volume.

Set `--lake-bin` (or `LAKE_BIN`) when a runner exposes Lake at a non-default
path; the Python interpreter is always checked for Python 3.11+.

`--dry-run` prints the selected branch and reviewer commands without creating
worktrees, running Lean, or writing data. `--build-docs` is intentionally
separate from the normal build because doc generation is expensive.

The static-site deployment entrypoint is also centralized:

```bash
./sdk/deploy/bin/reasbook-deploy docker --dry-run
./sdk/deploy/bin/reasbook-deploy docker --skip-build
```

The Docker adapter owns the Compose invocation and health probe; it invokes the
repository-specific `scripts/build/site.sh` pipeline. The image contains only
Nginx configuration, while the selected site is mounted read-only. The default
deployment is available at `http://127.0.0.1:3200/ReasBook/`; use `--port` to
change the host port. A custom packaged site requires `--skip-build`.

For immutable releases, use the release CLI rather than Compose directly:

```bash
# Verify and serve the GitHub candidate from the shared cache.
RELEASE_ID="${RELEASE_ID:?set RELEASE_ID to the generated release ID}"
./sdk/deploy/bin/reasbook-deploy release preview "$RELEASE_ID" --artifact pages

# Install the transferred full bundle, SHA256SUMS, and ReleaseSet. Obtain the
# policy digest from the trusted build channel, not from the transferred files.
POLICY_SHA256="${POLICY_SHA256:?set the trusted sha256 artifact-policy digest}"
FULL_BUNDLE="${RELEASE_ID}.site.tar.zst"
FULL_SHA256="$(awk -v bundle="$FULL_BUNDLE" \
  '$2 == bundle { print $1 }' SHA256SUMS)"
: "${FULL_SHA256:?SHA256SUMS has no matching full bundle}"
reasbook-deploy release install "$FULL_BUNDLE" \
  --sha256 "$FULL_SHA256" --release-set release-set.json \
  --artifact-policy-sha256 "$POLICY_SHA256" \
  --deploy-root /srv/reasbook \
  --health-url http://127.0.0.1/ReasBook/release-spec.json
```

After the pinned Pages workflow is merged to the GitHub default branch, run
`release configure-pages --profile github-pages --dry-run` and then the same
command without `--dry-run`. It creates only missing settings and fails closed
when a custom domain or any branch policy other than the exact default branch
already exists.

The installer lays the configured base path below
`/srv/reasbook/current/public`; point the static server at that stable document
root. See `config/deploy/nginx-self-hosted.conf`.

For the containerized production server, install the first release with the
explicit filesystem probe because no HTTP server exists yet:

```bash
RELEASE_ID="${RELEASE_ID:?set RELEASE_ID to the generated release ID}"
POLICY_SHA256="${POLICY_SHA256:?set the trusted sha256 artifact-policy digest}"
FULL_BUNDLE="${RELEASE_ID}.site.tar.zst"
FULL_SHA256="$(awk -v bundle="$FULL_BUNDLE" \
  '$2 == bundle { print $1 }' SHA256SUMS)"
: "${FULL_SHA256:?SHA256SUMS has no matching full bundle}"
reasbook-deploy release install "$FULL_BUNDLE" \
  --sha256 "$FULL_SHA256" --release-set release-set.json \
  --artifact-policy-sha256 "$POLICY_SHA256" \
  --deploy-root /srv/reasbook --filesystem-health-only
```

Then start the dedicated Compose project in one command:

```bash
REASBOOK_DEPLOY_ROOT=/srv/reasbook \
  docker compose -f docker-compose.self-hosted.yml up -d --wait
```

This production Compose file is separate from `docker-compose.yml`, which
remains the local generated-site preview. It mounts the entire deployment root
read-only and serves `/srv/reasbook/current/public`; do not bind-mount
`current/public` itself, because Docker would retain the symlink target chosen
when the container was created. Subsequent `release install` and `release
rollback` commands atomically replace `current`, and new Nginx requests observe
the new release without rebuilding or restarting the container. Use
`http://127.0.0.1:8080/ReasBook/release-spec.json` as the installer health URL;
override `REASBOOK_BIND_ADDRESS` or `REASBOOK_SELF_HOST_PORT` when placing the
container behind a reverse proxy. The default is a versioned stable Nginx
image; set `REASBOOK_NGINX_IMAGE` to an approved registry image or digest when
production policy requires a separately pinned supply chain.

After the container is healthy, use the HTTP probe for every install or
rollback so an invalid switch is automatically reverted:

```bash
reasbook-deploy release install "$FULL_BUNDLE" \
  --sha256 "$FULL_SHA256" --release-set release-set.json \
  --artifact-policy-sha256 "$POLICY_SHA256" \
  --deploy-root /srv/reasbook \
  --health-url http://127.0.0.1:8080/ReasBook/release-spec.json
```

The checksum and expected artifact-policy digest are trust inputs recorded on
the build/publish side. The destination rejects a ReleaseSet that does not bind
the full archive's checksum, ReleaseSpec, site digest, file count, byte count,
and policy before writing the deployment root. Every non-dry-run install needs
either an HTTP(S) health URL or the explicit bootstrap-only
`--filesystem-health-only` mode.

## CI helpers

CI behavior is implemented here and called directly:

```bash
reasbook-deploy ci verify-python
reasbook-deploy ci install-elan
reasbook-deploy ci prepare-cache v4.30.0
reasbook-deploy ci heartbeat LABEL COMMAND [ARGS...]
reasbook-deploy ci retry-143 COMMAND [ARGS...]
reasbook-deploy ci compress-cache PATH
reasbook-deploy ci decompress-cache PATH
```

These commands use argv vectors, validate branch/path inputs, and write
`GITHUB_ENV`/`GITHUB_PATH` only when those files are provided by the runner.

## Python API

```python
from pathlib import Path
from reasbook_deploy_sdk import DeploymentConfig, DeploymentPipeline, DeploymentService

config = DeploymentConfig(
    repo_root=Path("/work/ReasBook"),
    reviewer_root=Path("/work/Review/reasbook-reviewer"),
    data_root=Path("/work/Review/reasbook-reviewer/data"),
    cache_root=Path("/volume/math/users/zcwang/ReasBook_Reviewer/cache/reasbook"),
    books=("Analysis2_Tao_2022",),
    build=False,
)
report = DeploymentService(config).deploy()
```

Optional capability stages are explicit:

```python
from reasbook_deploy_sdk import DeploymentPipeline, TheoremGraphStage, VersoStage

pipeline = DeploymentPipeline((VersoStage(verso_builder), TheoremGraphStage(graph_generator)))
report = DeploymentService(config, pipeline=pipeline).deploy()
```

`DeploymentService` accepts injected Git, reviewer, and command ports, so
planning and failure handling can be tested without a network, Lean, or a
running reviewer.
