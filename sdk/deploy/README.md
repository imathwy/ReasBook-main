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
  -e sdk/theorem_graph -e sdk/comparator -e 'sdk/deploy[capabilities]'
```

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
./sdk/deploy/bin/reasbook-deploy release preview RELEASE_ID --artifact pages

# Install a transferred full bundle without requiring release-cache metadata.
FULL_SHA256="$(awk 'NR == 1 { print $1 }' SHA256SUMS)"
./sdk/deploy/bin/reasbook-deploy release install RELEASE_ID.site.tar.zst \
  --sha256 "$FULL_SHA256" --deploy-root /srv/reasbook \
  --health-url http://127.0.0.1/ReasBook/release-spec.json
```

The installer lays the configured base path below
`/srv/reasbook/current/public`; point the static server at that stable document
root. See `config/deploy/nginx-self-hosted.conf.example`.

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
