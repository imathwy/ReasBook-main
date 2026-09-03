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
| `full` | Every assembled project version, project-root API docs, Verso, theorem maps, and explicit dependency stubs | Self-hosted server |
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

Configure the repository once with **Settings → Pages → GitHub Actions**. Then
publish the already-built Pages artifact:

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

The workflow checks the tag target, all digests and identities, the 850 MB
site budget, and the 60,000-file budget before calling the official Pages
deployment action. It performs no source build. Publishing an existing tag is
idempotent only when every remote asset has the same name, size, and digest;
assets are never overwritten.

Before creating a new tag, the publisher requires a clean local checkout whose
`HEAD` is the current GitHub default-branch commit. This prevents a feature
branch from accidentally tagging an unpublished tree. Every dispatch uses the
current trusted workflow and rejects a release tag that is not on that
default-branch history. Once an immutable release exists, an exact re-dispatch
is allowed from another local branch because the tag ancestry and every remote
asset digest are revalidated remotely.

Both artifacts preserve project content and close referenced URLs. A link to
an API page outside the selected project roots resolves to a small explanatory
page, not a 404. The `full` artifact additionally retains every assembled
project version; the Pages projection retains only explicit canonical versions.

## Self-hosted installation

Install the full artifact directly from the release cache:

```bash
./sdk/deploy/bin/reasbook-deploy release publish RELEASE_ID \
  --target self-hosted --deploy-root /srv/reasbook \
  --health-url http://127.0.0.1/ReasBook/release-spec.json
```

For a separate server, transfer the full archive and its checksum, install the
deploy SDK, and run the portable command:

```bash
FULL_SHA256="$(awk 'NR == 1 { print $1 }' SHA256SUMS)"
./sdk/deploy/bin/reasbook-deploy release install \
  RELEASE_ID.site.tar.zst --sha256 "$FULL_SHA256" \
  --deploy-root /srv/reasbook \
  --health-url http://127.0.0.1/ReasBook/release-spec.json
```

Configure the web server once with `/srv/reasbook/current/public` as its
document root. `config/deploy/nginx-self-hosted.conf.example` is a ready
starting point. The installer verifies and extracts on the destination
filesystem, writes an immutable version directory, atomically replaces the
`current` symlink, and restores the preceding link when the health probe fails.

Rollback never rebuilds:

```bash
./sdk/deploy/bin/reasbook-deploy release rollback \
  --target self-hosted --deploy-root /srv/reasbook --to RELEASE_ID
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
documentation stage handles all explicit project roots for that branch and
publishes its result atomically. The local orchestrator defaults to three
branch workers and a 12-hour branch-documentation timeout; both remain
explicit CLI options for unusually small or large releases.

## Security and failure behavior

- Credentials come only from `gh`/`GH_TOKEN`; they are absent from profiles,
  specs, manifests, archive commands, and logs.
- Archive members are rejected when they contain traversal paths, links, or
  special files.
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
