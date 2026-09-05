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
# Packaging requires a completed aggregate `site` stage; branch Lean caches
# alone are not sufficient. Confirm state, then derive both immutable bundles.
RELEASE_ID="${RELEASE_ID:?set RELEASE_ID to the generated release ID}"
./sdk/deploy/bin/reasbook-deploy release status "$RELEASE_ID"
./sdk/deploy/bin/reasbook-deploy release package "$RELEASE_ID"

# Verify both archives, exercise both preview shapes, and smoke-test an atomic
# self-hosted install. This uses cache/reasbook/validation and does not rebuild.
./sdk/deploy/bin/reasbook-deploy release validate "$RELEASE_ID" \
  --browser-mode required

# Serve the exact GitHub candidate from the shared cache for manual inspection.
./sdk/deploy/bin/reasbook-deploy release preview "$RELEASE_ID" --artifact pages

# On the trusted build host, record the per-release full-bundle SHA-256 and the
# policy digest. Deliver both independently of the transferred bundle/ReleaseSet.
POLICY_SHA256="$(./sdk/deploy/bin/reasbook-deploy release \
  --repo-root . policy-digest --profile github-pages)"
CACHE_ROOT="${REASBOOK_CACHE_ROOT:-/volume/math/users/zcwang/ReasBook_Reviewer/cache/reasbook}"
TRUSTED_FULL_BUNDLE="$CACHE_ROOT/releases/$RELEASE_ID/$RELEASE_ID.site.tar.zst"
FULL_SHA256="$(sha256sum "$TRUSTED_FULL_BUNDLE" | awk '{print $1}')"

# On the destination, FULL_SHA256 must come from that authenticated record.
FULL_BUNDLE="${RELEASE_ID}.site.tar.zst"
FULL_SHA256="${FULL_SHA256:?set the independently authenticated full-bundle SHA-256}"
reasbook-deploy release install "$FULL_BUNDLE" \
  --expected-bundle-sha256 "$FULL_SHA256" --release-set release-set.json \
  --artifact-policy-sha256 "$POLICY_SHA256" \
  --deploy-root /srv/reasbook \
  --health-url http://127.0.0.1/ReasBook/release-spec.json
```

`release validate` does not rebuild. It fully extracts and verifies the `pages`
archive, verifies and installs the `full` archive through the production atomic
installer, then serves both with the repository preview adapter in strict
production-routing mode. Unprefixed development aliases are unavailable, and
the base path without its trailing slash must return the same permanent
redirect as the production server. It checks the
catalog, canonical project, documentation, Verso, theorem-map, asset,
ReleaseSpec, and 404 routes. It also checks every version root, every project
version in `full`, and the canonical project versions in `pages`. Successful
runs remove the large scratch trees and retain a small result/log directory below
`cache/reasbook/validation/<release-id>/`; failures retain the exact scratch
tree for diagnosis. Pass `--keep-workdir` to retain a successful scratch tree.
The per-project Verso exception comes from the existing
`scripts/pages/project_catalog.py` capability registry used by assembly and
the remote build service. Validation reads it only from the release-scoped tooling snapshot whose
SHA-256 is embedded in the ReleaseSpec. For a local canary without a snapshot,
the current checkout is accepted only when its complete tooling digest is an
exact match, so capability policy cannot drift after packaging.

Browser checks are optional so the deployment SDK keeps no mandatory browser
runtime. `--browser-mode auto` (the default) runs Playwright when both its
Python package and Chromium are installed, and reports an explicit skip when
either is absent. Other launch or browser failures still fail the gate. For the
pre-publication gate, install both once, then require the browser check:

```bash
./sdk/common/bin/python -m pip install -e 'sdk/deploy[e2e]'
./sdk/common/bin/python -m playwright install chromium
./sdk/deploy/bin/reasbook-deploy release validate "$RELEASE_ID" \
  --browser-mode required
```

Using the shared interpreter wrapper ensures Playwright is installed into the
same Python selected by the CLI. The required browser pass opens every route
kind at desktop and 390 px mobile widths, records screenshots, rejects HTTP and
transport-level same-origin request failures and console/page errors, verifies
that every final URL stays within the configured base path, and checks each
representative page for horizontal overflow.
Use `--browser-mode skip` only when a separate browser E2E run is recorded.

After the pinned Pages workflow is merged to the GitHub default branch, run
`release configure-pages --profile github-pages --dry-run` and then the same
command without `--dry-run`. It creates only missing settings and fails closed
when a custom domain or any branch policy other than the exact default branch
already exists. It also audits and enables repository immutable releases; the
GitHub token needs repository Administration read permission for both dry-run
and publication, and write permission for the one-time enable operation.
An obsolete policy can be removed only when it is the sole policy beside the
default branch, using `--remove-policy-id ID --expected-policy-name NAME
--expected-policy-type branch|tag`. All three values are mandatory; run the
exact command with `--dry-run` first. The implementation compares every field,
refuses the default branch and multi-policy cleanup, deletes only `/ID`, and
re-fetches the complete list before reporting success. Enabling immutable
releases also has a bounded eventual-consistency wait: 300 seconds by default,
polled every five seconds. Override it with
`--immutable-convergence-timeout-seconds` and
`--immutable-convergence-poll-seconds`; values must be positive and finite,
with a poll interval of at least one second that does not exceed the timeout.
GitHub control-plane commands require an authenticated GitHub CLI 2.93.0 or
newer on `PATH`; credentials may be supplied with `GH_TOKEN` and are never
written into a ReleaseSpec or bundle.

Promote the already packaged and browser-validated Pages artifact with one
command:

```bash
./sdk/deploy/bin/reasbook-deploy release publish "$RELEASE_ID" \
  --target github-pages --dry-run
./sdk/deploy/bin/reasbook-deploy release publish "$RELEASE_ID" \
  --target github-pages --wait
```

The dry-run is a read-only publication preflight, not an offline preview. For
a new Release it verifies the same clean local `HEAD`, exact GitHub
default-branch commit, optional tag target, accepted package, and immutable
release setting required by the real publication. For an existing Release it
also validates the tag and every present asset. It never creates or edits a
tag or Release, uploads an asset, or dispatches the Pages workflow.

This is one-command *promotion*, not a source-to-production build:
`configure-pages` is a separate one-time idempotent setup, and the configured
remote build service's build,
aggregate, package, and required acceptance gate must already be complete. The
local publisher uploads four Release assets; the workflow verifies their
release attestations, downloads and extracts the Pages archive, uploads the
static tree, and deploys Pages. Neither side runs Lean, Verso, doc-gen, or a
theorem graph. Runtime depends mainly on the archive/uplink, Actions queue, and
Pages deployment; CPU is limited to hashing, validation, and decompression.
The workflow explicitly grants `attestations: read` and installs pinned
`PyYAML==6.0.3` for the trusted policy check. Release uploads use a bounded
two-hour timeout (ordinary API calls remain five minutes) because transfer time
for the allowed large archive is network-dominated.

The Pages capacity policy is single-source: local packaging, local acceptance,
and the workflow's `release verify --profile github-pages --artifact-policy
pages` use the same checked-in 920 MB, 60,000-file, and
180,000-archive-member operational limits. A separate 1 GB hard gate is
enforced even if the operational policy is later raised. A bundle that the
workflow would reject cannot pass local packaging merely because a verifier
default was looser.

When `--wait` is present, the command first waits up to 1,800 seconds for the
workflow and then up to 300 seconds for the public Pages ReleaseSpec to
converge. It verifies the exact release ID, ReleaseSpec digest, and registry
commit before recording `published`; stale CDN content and network failures are
retried but fail closed at the deadline. Override only the second deadline with
`--pages-health-timeout-seconds SECONDS`.

The installer lays the configured base path below
`/srv/reasbook/current/public`; point the static server at that stable document
root. See `config/deploy/nginx-self-hosted.conf`.

The portable `release install` command above consumes the same packaged `full`
bundle paired with the Pages artifact. After transfer and one-time server
configuration, that single command verifies the independently authenticated
per-release checksum and the policy, stages the release, and atomically switches
`current`; it performs no rebuild. A co-transferred `SHA256SUMS` is useful only
for diagnostics and must not be the source of `FULL_SHA256`. The policy digest
checks deployment policy; because it can be shared by many releases, it does
not authenticate release identity.

For the containerized production server, install the first release with the
explicit filesystem probe because no HTTP server exists yet:

```bash
RELEASE_ID="${RELEASE_ID:?set RELEASE_ID to the generated release ID}"
POLICY_SHA256="${POLICY_SHA256:?set the trusted sha256 artifact-policy digest}"
FULL_SHA256="${FULL_SHA256:?set the independently authenticated full-bundle SHA-256}"
FULL_BUNDLE="${RELEASE_ID}.site.tar.zst"
reasbook-deploy release install "$FULL_BUNDLE" \
  --expected-bundle-sha256 "$FULL_SHA256" --release-set release-set.json \
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
  --expected-bundle-sha256 "$FULL_SHA256" --release-set release-set.json \
  --artifact-policy-sha256 "$POLICY_SHA256" \
  --deploy-root /srv/reasbook \
  --health-url http://127.0.0.1:8080/ReasBook/release-spec.json
```

The per-release checksum and expected artifact-policy digest are trust inputs
recorded on the build/publish side and delivered independently of the archive.
The destination rejects a ReleaseSet that does not bind the full archive's
checksum, ReleaseSpec, site digest, file count, byte count, and policy before
writing the deployment root. Every non-dry-run install needs either an HTTP(S)
health URL or the explicit bootstrap-only `--filesystem-health-only` mode.
The parser applies the same exactly-one requirement to self-hosted `publish`
and `rollback` commands, including dry runs, so they cannot defer the health
decision until activation.

The Pages publisher, including `--dry-run`, requires the successful
`validation/<release-id>/latest.json` produced by `release validate
--browser-mode required`. The self-hosted `release publish` path consumes the
same record. The portable `release install` boundary instead requires the
externally supplied full-bundle SHA-256 and policy digest shown above; it never
accepts either value solely from the transferred ReleaseSet.

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
