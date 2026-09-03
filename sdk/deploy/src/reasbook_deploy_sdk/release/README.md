# Static Release Context

This package turns remotely built ReasBook output into immutable artifacts for
GitHub Pages and project-owned static servers. It is separate from the
selected-book reviewer deployment.

## Architecture

```text
profile + canonical map + Git refs
                 |
                 v
          immutable ReleaseSpec
                 |
       SiFlow build + aggregate
                 |
          verified full site
             /         \
      full artifact   Pages projection
             \         /
               ReleaseSet
             /           \
  atomic self-host     GitHub Release
                           |
                    publish-only Pages
```

The domain models and planner do not start processes or access GitHub. Git
object reads, branch builds, site projection, archive verification, GitHub
publication, and self-hosted installation are separate adapters.

The two artifacts have deliberately different content contracts:

| Name | Contract | Intended target |
| --- | --- | --- |
| `full` | Every assembled project version, reachable project-module API docs, Verso, theorem maps, and explicit dependency stubs | Self-hosted server |
| `pages` | Canonical project versions with the same bounded, link-closed documentation | GitHub Pages |

Both retain the `/ReasBook/` public base path. `release-set.json` binds their
bundle hashes, site-tree hashes, sizes, and projection-policy hash to one
`ReleaseSpec`.

## Configuration

- `config/deploy/github-pages.yml` defines release, artifact, and publisher
  policy.
- `config/toolchains.yml` is the branch registry.
- `config/canonical-projects.yml` selects the public version of projects found
  on multiple active branches.
- `config/schemas/release-spec.schema.json` documents immutable build identity.
- `config/schemas/release-set.schema.json` documents target artifact identity.

Canonical selection never silently falls back to another branch. Changing an
artifact policy also produces a new release instead of mutating an existing
one.

## Production workflow

Resolve moving refs before submitting remote work:

```bash
./sdk/deploy/bin/reasbook-deploy release plan \
  --profile github-pages --fetch
```

Production project builds and branch finalizers run through the private SiFlow
operations layer. The aggregate result is copied into the release's `site/`
directory and marked validated. GitHub Actions never receives Lean caches or
build credentials.

Package and inspect both target artifacts:

```bash
./sdk/deploy/bin/reasbook-deploy release package RELEASE_ID
./sdk/deploy/bin/reasbook-deploy release status RELEASE_ID
```

Packaging is incremental. A bundle is reused only when its archive checksum,
embedded manifest, ReleaseSpec, extracted tree digest, and artifact identity
all verify. Otherwise that artifact is regenerated; a valid sibling artifact
is retained.

`release deploy` remains a convenience for a small local canary. Do not use it
for a full public build:

```bash
./sdk/deploy/bin/reasbook-deploy release deploy \
  --profile github-pages --only papers/PROJECT_ID \
  --max-parallel-branches 3 --no-publish
```

## Local preview

Preview the exact tree bound to a packaged archive:

```bash
./sdk/deploy/bin/reasbook-deploy release preview RELEASE_ID \
  --artifact pages --host 127.0.0.1 --port 18000
```

Open `http://127.0.0.1:18000/ReasBook/`. Before starting the server, the CLI
checks the bundle SHA-256 and compares the local tree's hash, file count, and
byte count with the embedded manifest. Use `--artifact full` for the
self-hosted candidate.

For a path-based workspace proxy, bind all interfaces and provide the external
prefix removed by that proxy:

```bash
./sdk/deploy/bin/reasbook-deploy release preview RELEASE_ID \
  --artifact pages --host 0.0.0.0 --port 3000 \
  --public-prefix /workspace/proxy/3000
```

`--public-prefix` changes responses only; it never rewrites the bundle.

## GitHub Pages publication

Once the workflow is on the default branch, configure and audit Pages, then
publish the already-built artifact:

```bash
./sdk/deploy/bin/reasbook-deploy release configure-pages \
  --profile github-pages --dry-run
./sdk/deploy/bin/reasbook-deploy release configure-pages \
  --profile github-pages
```

Configuration is idempotent and fail-closed. It creates only missing
workflow-based Pages/environment settings, permits only the exact default
branch, and refuses to overwrite custom domains or incompatible/extra branch
policies.

```bash
./sdk/deploy/bin/reasbook-deploy release publish RELEASE_ID \
  --target github-pages --wait
```

The publisher creates an immutable tag and GitHub Release, uploads exactly
four files, and dispatches `.github/workflows/publish_release_pages.yml` from
the repository's current default branch:

```text
RELEASE_ID.pages.site.tar.zst
release-manifest.json
release-set.json
SHA256SUMS
```

The local publisher checks the configured policy digest and both artifact
records before upload. The workflow independently checks the tag target, the
Pages archive/manifest/spec/ReleaseSet bindings, the shape of the full record
and policy digest, the 850 MB site budget, and the 60,000-file budget before
calling the official Pages deployment action. It has no full archive and
performs no source build. Publishing an existing tag is
idempotent only when every remote asset has the same name, size, and digest;
assets are never overwritten.

Before creating a new tag, the publisher requires a clean local checkout whose
`HEAD` is the current GitHub default-branch commit. This prevents a feature
branch from accidentally tagging an unpublished tree. Every dispatch uses the
current trusted workflow and rejects a release tag that is not on that
default-branch history. Once an immutable release exists, an exact re-dispatch
is allowed from another local branch because the tag ancestry and every remote
asset digest are revalidated remotely.

Both artifacts preserve project content and close referenced URLs. API docs
start at each configured entry root and include every reachable project-owned
module, processed in batches of at most 128; Mathlib, Lean, and other external
libraries are not rendered. A referenced external API page resolves to a small
explanatory stub, not a 404. Modern doc-gen renders a trimmed database and the
legacy adapter renders the same bounded set through its compatibility path.
The `full` artifact additionally retains every assembled project version; the
Pages projection retains only explicit canonical versions.

## Self-hosted installation

Install the full artifact directly from the release cache:

```bash
./sdk/deploy/bin/reasbook-deploy release publish RELEASE_ID \
  --target self-hosted --deploy-root /srv/reasbook \
  --health-url http://127.0.0.1/ReasBook/release-spec.json
```

For a separate server, transfer the full archive, its matching `SHA256SUMS`,
and `release-set.json`; obtain the expected artifact-policy digest separately
from the trusted build side. Install the deploy SDK and run:

```bash
RELEASE_ID="${RELEASE_ID:?set RELEASE_ID to the generated release ID}"
POLICY_SHA256="${POLICY_SHA256:?set the trusted sha256 artifact-policy digest}"
FULL_BUNDLE="${RELEASE_ID}.site.tar.zst"
FULL_SHA256="$(awk -v bundle="$FULL_BUNDLE" \
  '$2 == bundle { print $1 }' SHA256SUMS)"
: "${FULL_SHA256:?SHA256SUMS has no matching full bundle}"
reasbook-deploy release install \
  "$FULL_BUNDLE" --sha256 "$FULL_SHA256" \
  --release-set release-set.json \
  --artifact-policy-sha256 "$POLICY_SHA256" \
  --deploy-root /srv/reasbook \
  --health-url http://127.0.0.1/ReasBook/release-spec.json
```

Configure the web server once with `/srv/reasbook/current/public` as its
document root. `config/deploy/nginx-self-hosted.conf` is a ready
starting point. Record the checksum and expected policy digest on the trusted
build/publish side. Before creating the deployment root, the installer verifies
the archive and binds its checksum, ReleaseSpec, site digest, file/byte totals,
and policy to the transferred ReleaseSet. It extracts into a staging directory,
writes an immutable version directory, atomically replaces the `current`
symlink, and restores the preceding link when the health probe fails. Use
`--filesystem-health-only` explicitly only while bootstrapping a server that
cannot yet answer an HTTP(S) health request.

Rollback never rebuilds:

```bash
./sdk/deploy/bin/reasbook-deploy release rollback \
  --target self-hosted --deploy-root /srv/reasbook --to RELEASE_ID \
  --health-url http://127.0.0.1/ReasBook/release-spec.json
```

Do not bind-mount `current/public/ReasBook` directly into a long-running
container: container runtimes may resolve that symlink only when the mount is
created. Mount `/srv/reasbook` as a whole and point the in-container server at
`/srv/reasbook/current/public`, or run Nginx directly on the host.

## Persistent state

```text
cache/reasbook/releases/<release-id>/
  release-spec.json
  profile.yml
  toolchains.yml
  canonical-projects.yml
  state.json
  worktrees/
  logs/
  branches/
  site/                              complete aggregate tree
  release-manifest.json             full manifest
  <release-id>.site.tar.zst          full bundle
  SHA256SUMS
  bundle.json
  artifacts/pages/
    site/                            bounded Pages projection
    release-manifest.json
    <release-id>.pages.site.tar.zst
    SHA256SUMS
    bundle.json
  release-set.json
  publication.json
```

Branches may run in parallel; stages within one branch stay ordered. Each
branch receives an isolated writable Lake-cache namespace. One bounded
documentation stage handles the reachable project-module closure of all entry
roots for that branch and publishes its `project-modules-v2` cache atomically.
The local orchestrator defaults to three branch workers and a 12-hour
branch-documentation timeout; both remain explicit CLI options for unusually
small or large releases.

## Security and failure behavior

- Credentials come only from `gh`/`GH_TOKEN`; they are absent from profiles,
  specs, manifests, archive commands, and logs.
- Archive members are rejected before extraction when they contain traversal
  aliases, links, special files, invalid names, or exceed fixed count/byte
  limits. Both embedded JSON metadata files have independent pre-read limits.
- A Pages link that escapes the configured base path aborts projection.
- A failed package, upload, health check, or symlink switch leaves the previous
  published target intact.
- Old schema-version-1 full manifests remain readable as `full` artifacts.

## Prerequisites

- Python 3.11 or newer.
- GNU tar with `--zstd` and the deploy SDK dependencies.
- All registered version branches fetched before planning.
- An authenticated GitHub CLI with Release upload and workflow-dispatch access
  for GitHub publication.
- Enough self-hosted disk space for the incoming archive, extracted release,
  safety margin, and currently active release.

The hosting rationale and rejected alternatives are recorded in
[`ADR-0001`](../../../../../docs/decisions/0001-static-release-pipeline.md) and
[`ADR-0002`](../../../../../docs/decisions/0002-target-specific-release-artifacts.md).
