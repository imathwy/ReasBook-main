# Static Release Context

This package builds immutable public ReasBook sites. It is intentionally
separate from the selected-book reviewer deployment.

## Boundaries

```text
profile + canonical map + Git refs
                 |
                 v
          immutable ReleaseSpec
                 |
       +---------+----------+
       |                    |
 local branch builder   future executor
       |
 canonical/versioned site
       |
 verified tar.zst bundle
       |
 GitHub Release -> publish-only Pages workflow
```

The domain models and planner do not start processes or access GitHub. Git
object reads, local branch builds, archive handling, and GitHub publication are
separate adapters.

## Configuration

- `config/deploy/github-pages.yml` defines site policy and the publisher.
- `config/toolchains.yml` is the branch registry.
- `config/canonical-projects.yml` is mandatory for projects found on multiple
  active branches.
- `config/schemas/release-spec.schema.json` documents the immutable output.

Canonical failure never silently falls back to an older branch.

## Commands

```bash
# Resolve moving refs to commits without building.
./sdk/deploy/bin/reasbook-deploy release plan --profile github-pages
./sdk/deploy/bin/reasbook-deploy release plan --profile github-pages --fetch
./sdk/deploy/bin/reasbook-deploy release build RELEASE_ID --dry-run

# Small local canary: build, package, upload, and dispatch Pages.
./sdk/deploy/bin/reasbook-deploy release deploy \
  --profile github-pages --max-parallel-branches 3 --wait

# Production: publish an existing bundle assembled from SiFlow results.
./sdk/deploy/bin/reasbook-deploy release publish RELEASE_ID --wait

# Resume or inspect a persisted release.
./sdk/deploy/bin/reasbook-deploy release status RELEASE_ID
./sdk/deploy/bin/reasbook-deploy release resume RELEASE_ID --wait
./sdk/deploy/bin/reasbook-deploy release rollback --to RELEASE_ID --wait

# Verify a downloaded asset without GitHub access.
./sdk/deploy/bin/reasbook-deploy release verify SITE.tar.zst \
  --sha256 EXPECTED_SHA256 --extract-to /tmp/reasbook-site
```

Use `--only books/PROJECT_ID` to build a small release. `--dry-run` on
`release deploy` resolves and prints the spec without creating release state.
One-click deploy fetches `origin` first; use `--no-fetch` for an offline
checkout. Do not use `release deploy` for a full public multi-version build:
production branch builds and finalizers run through the private SiFlow
operations layer, and only its verified aggregate bundle is passed to
`release publish`.

## Preview the publish candidate

Preview the verified bundle rather than an intermediate build directory. This
checks the same static tree that the Pages workflow will extract:

```bash
export REASBOOK_CACHE_ROOT=/path/to/reasbook-cache
RELEASE_ID=site-YYYYMMDDTHHMMSSZ-xxxxxxxxxxxx
RELEASE_DIR="$REASBOOK_CACHE_ROOT/releases/$RELEASE_ID"
BUNDLE="$RELEASE_DIR/$RELEASE_ID.site.tar.zst"
SHA256="$(awk 'NR == 1 { print $1 }' "$RELEASE_DIR/SHA256SUMS")"
PREVIEW="$REASBOOK_CACHE_ROOT/previews/$RELEASE_ID"

./sdk/deploy/bin/reasbook-deploy release verify \
  "$BUNDLE" --sha256 "$SHA256" --extract-to "$PREVIEW"

REASBOOK_SITE_DIR="$PREVIEW" \
REASBOOK_DOC_SOURCE="$PREVIEW/docs" \
./sdk/common/bin/python ./scripts/preview/serve.py 18000 \
  --site-root /ReasBook/
```

Open `http://127.0.0.1:18000/ReasBook/`. Check the catalog, a canonical
project, a version-qualified project, API documentation, Verso output, and a
theorem map before publication.

For a path-based workspace proxy, also bind the workspace interface and pass
the external path that the proxy removes:

```bash
REASBOOK_SITE_DIR="$PREVIEW" \
REASBOOK_DOC_SOURCE="$PREVIEW/docs" \
./sdk/common/bin/python ./scripts/preview/serve.py 3000 \
  --host 0.0.0.0 --site-root /ReasBook/ \
  --public-prefix /workspace/proxy/3000
```

This changes responses only; the verified bundle remains byte-for-byte
unchanged.

## GitHub hosting limits

GitHub Release and GitHub Pages impose different limits. Each Release asset
must be under 2 GiB, while the **extracted published Pages tree** must be under
1 GB and a Pages deployment must finish within 10 minutes. The release profile
currently bounds compressed bundle size and file count; before publishing to
Pages, also measure the extracted preview and keep a margin below the Pages
limit:

```bash
du -sb "$PREVIEW"
find "$PREVIEW" -type f | wc -l
```

Use 950,000,000 bytes as the operational ceiling for the temporary Pages
target. If the preview is larger, keep the immutable bundle in GitHub Release
and publish a slim catalog, or deploy the complete bundle to the self-hosted
target. A successful Release upload does not prove that Pages can accept the
site.

- [GitHub Pages limits](https://docs.github.com/en/pages/getting-started-with-github-pages/github-pages-limits)
- [GitHub Release limits](https://docs.github.com/en/repositories/releasing-projects-on-github/about-releases)

## Persistent State

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
  site/
  build-report.json
  release-manifest.json
  <release-id>.site.tar.zst
  SHA256SUMS
  bundle.json
  publication.json
```

Branches run in parallel; stages within one branch remain ordered. Each branch
gets an isolated writable Lake cache namespace. Documentation targets run one
at a time inside their branch.

The GitHub adapter reads credentials only through `gh`/`GH_TOKEN`; credentials
are never represented in the profile, ReleaseSpec, manifest, or command logs.

## Prerequisites

- Fetch every registered version branch before planning: `git fetch --all`.
- Use Python 3.11+ and install the deploy capability dependencies.
- GNU tar must support `--zstd`.
- Publishing requires `gh auth status` to succeed with Release upload and
  Actions workflow-dispatch permission.

GitHub Actions never receives Lean credentials or build caches. It only
downloads and verifies the three immutable Release assets. The release tag
uniquely determines the bundle name; `SHA256SUMS`, the external manifest, the
manifest embedded in the archive, and `release-spec.json` must all agree.
Publishing an existing tag is idempotent only when every asset name, size, and
GitHub SHA-256 digest is unchanged. Assets are never overwritten.

The superseded GitHub-hosted Lean builders (`deploy_pages.yml`,
`deploy_preview.yml`, and `docs_full.yml`) are removed. Production deployments
use only `publish_release_pages.yml`. New Release tags are pinned to the exact
commit currently at the trusted default branch; publication and rollback run
the workflow from that immutable tag and verify that the tag resolves to the
workflow's `GITHUB_SHA`. All expensive Lean and documentation work happens
before publication.
