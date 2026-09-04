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

After `release status` reports a completed aggregate `site` stage, package and
inspect both target artifacts. Branch-level Lean caches without that aggregate
site are not sufficient:

```bash
./sdk/deploy/bin/reasbook-deploy release status RELEASE_ID
./sdk/deploy/bin/reasbook-deploy release package RELEASE_ID
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

For a completed release in the local cache, the exact package, required
acceptance, and manual-preview sequence is:

```bash
RELEASE_ID="${RELEASE_ID:?set RELEASE_ID to the generated release ID}"
./sdk/deploy/bin/reasbook-deploy release package "$RELEASE_ID"
./sdk/deploy/bin/reasbook-deploy release validate "$RELEASE_ID" \
  --browser-mode required
./sdk/deploy/bin/reasbook-deploy release preview "$RELEASE_ID" \
  --artifact pages --host 127.0.0.1 --port 18000
```

The SDK defaults to
`/volume/math/users/zcwang/ReasBook_Reviewer/cache/reasbook`; set
`REASBOOK_CACHE_ROOT` or pass the release-level `--cache-root` before the
subcommand on another host or volume.

This command does not rebuild. It verifies both archives and their ReleaseSet,
serves the Pages projection, installs the full artifact through the atomic
self-hosted adapter, and serves that installed tree. HTTP checks cover every
declared project-version entry appropriate to each artifact; Playwright opens
one representative of every route kind at both desktop and 390 px widths.
Per-project Verso exceptions are loaded from the tooling snapshot cryptographically
bound to the ReleaseSpec, never from an unrelated current checkout.

To start the same preview again without rerunning acceptance:

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
branch, enables repository immutable releases, and refuses to overwrite custom
domains or incompatible/extra branch policies. The caller needs repository
Administration read permission to audit the immutable-release setting and
write permission to enable it.

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

The local publisher first requires the browser-complete acceptance record for
the current package, then checks the configured policy digest and both artifact
records before upload. Dry-run crosses the same evidence and
repository-setting gates. The publisher waits for GitHub to report the Release
immutable before dispatch. After upload succeeds but before the draft is
published, it re-reads the same draft ID/tag and requires all four remote asset
sizes and server-computed digests to match. The workflow uses GitHub's Release
and per-asset verification commands, independently checks the tag target,
archive/manifest/spec/ReleaseSet bindings, and recomputes the policy digest
from its trusted checked-out profile. It enforces the compressed,
archive-member, 850 MB site, and 60,000-file budgets before extraction. It has
no full archive and performs no source build. Publishing an existing tag is
idempotent only when every remote asset has the same name, size, and digest;
assets are never overwritten, and an already-published Release is not edited
before re-dispatch.

The GitHub path is a one-command promotion of an already packaged and accepted
release, not a source-to-production one-click build. `configure-pages` is a
separate one-time idempotent setup. Publication uploads the four assets, then
the workflow downloads/verifies the Pages archive, extracts it once, uploads
the static tree, and deploys Pages. It never receives Lean caches and runs no
Lean, Verso, doc-gen, or theorem-graph build. Elapsed time is therefore driven
mainly by archive size and uplink, Actions queueing, decompression/upload, and
the Pages deploy; runner CPU is limited to hashing, verification, and
extraction. The local upload has a two-hour failure timeout while normal GitHub
API calls retain a five-minute timeout. The verify job declares read-only
`contents`, `pages`, and `attestations` permissions, and installs only pinned
`PyYAML==6.0.3` for the SDK policy check.

Before creating a new tag, the publisher requires a clean local checkout whose
`HEAD` is both the current GitHub default-branch commit and the ReleaseSpec's
exact `source.registry_commit`. This prevents a feature branch or a newer main
checkout from attaching a validated bundle to a different source revision.
Local canaries may use a dirty tooling snapshot, but GitHub publication requires
the exact clean `COMMIT+tooling-sha256:DIGEST` revision form. The publisher
atomically creates the Git ref before the draft Release, invokes Release
creation and publication through the REST API, and rechecks the fully
dereferenced target before upload, publication, and dispatch. Release upload
and workflow dispatch use only flags supported by GitHub CLI 2.4; wait-mode run
discovery also reads the Actions REST API instead of version-specific CLI JSON
fields. A pre-existing tag or a tag won by a
concurrent creator is accepted only if it resolves to the ReleaseSpec commit.
Every dispatch uses the current
trusted workflow, which independently repeats the source-commit and
clean-tooling checks and requires the tag to remain on default-branch history.
Once an immutable release exists, an exact re-dispatch is allowed from another
local branch because the tag identity, ancestry, and every remote asset digest
are revalidated remotely. The workflow deliberately anchors policy to its
current trusted default-branch profile. If that policy changed since an older
Release was built, do not re-dispatch it; create and validate a new ReleaseSpec.

The v5 Pages uploader includes digest-verified hidden files such as `.nojekyll`
and `.well-known/`. Packaging rejects exact `.git` or `.github` path segments,
which GitHub excludes even in hidden-file mode, so the uploaded tree cannot
silently differ from the locally verified tree.

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

For a separate server, transfer the full archive and `release-set.json`. On the
trusted build side, record both the archive's per-release SHA-256 and the
expected artifact-policy digest before the transfer. Deliver those values to
the destination operator through an independent authenticated channel:

```bash
POLICY_SHA256="$(./sdk/deploy/bin/reasbook-deploy release \
  --repo-root . policy-digest --profile github-pages)"
CACHE_ROOT="${REASBOOK_CACHE_ROOT:-/volume/math/users/zcwang/ReasBook_Reviewer/cache/reasbook}"
FULL_BUNDLE="$CACHE_ROOT/releases/$RELEASE_ID/$RELEASE_ID.site.tar.zst"
FULL_SHA256="$(sha256sum "$FULL_BUNDLE" | awk '{print $1}')"
printf 'release=%s\nfull_sha256=%s\npolicy_sha256=%s\n' \
  "$RELEASE_ID" "$FULL_SHA256" "$POLICY_SHA256"
```

Then install the deploy SDK on the destination and run:

```bash
RELEASE_ID="${RELEASE_ID:?set RELEASE_ID to the generated release ID}"
POLICY_SHA256="${POLICY_SHA256:?set the trusted sha256 artifact-policy digest}"
FULL_SHA256="${FULL_SHA256:?set the independently authenticated full-bundle SHA-256}"
FULL_BUNDLE="${RELEASE_ID}.site.tar.zst"
reasbook-deploy release install \
  "$FULL_BUNDLE" --expected-bundle-sha256 "$FULL_SHA256" \
  --release-set release-set.json \
  --artifact-policy-sha256 "$POLICY_SHA256" \
  --deploy-root /srv/reasbook \
  --health-url http://127.0.0.1/ReasBook/release-spec.json
```

This is the same `full` bundle produced in the ReleaseSet beside the Pages
artifact. After transfer and one-time web-server setup, `release install` is
the single atomic activation command: it validates the external trust inputs,
stages the tree, switches `current`, and probes health without rebuilding.
Do not derive `FULL_SHA256` from a `SHA256SUMS` file transferred with the
archive; an attacker could replace both. Such a file is only diagnostic.
`POLICY_SHA256` verifies deployment policy but, because it can remain constant
across releases, it does not authenticate release identity.

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
