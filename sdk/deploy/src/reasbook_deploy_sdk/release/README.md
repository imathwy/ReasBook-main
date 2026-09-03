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

# One-click local build, package, upload, and Pages dispatch.
./sdk/deploy/bin/reasbook-deploy release deploy \
  --profile github-pages --max-parallel-branches 3 --wait

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
checkout.

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
