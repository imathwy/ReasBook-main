# ADR-0001: Build remotely and publish immutable static releases

## Status

Accepted

## Date

2026-09-03

## Context

ReasBook spans several Lean/mathlib versions. The same book may exist on more
than one version branch, full documentation builds are expensive, and GitHub
Pages is only a temporary hosting target. Rebuilding Lean inside GitHub Actions
would duplicate work, make cache behavior runner-dependent, and couple the
site artifact to GitHub's compute environment.

## Decision

- Version branches own Lean sources and pin their full commit, toolchain, and
  `lake-manifest.json` digest in a `ReleaseSpec`.
- Duplicate projects select exactly one explicit canonical version; other
  versions remain available below version-qualified routes.
- Project builds and branch finalization run on SiFlow and reuse the external
  cache at `/volume/math/users/zcwang/ReasBook_Reviewer/cache/reasbook`.
- A single aggregate job assembles and verifies the complete static tree.
- GitHub Releases store the immutable bundle, release manifest, and checksums.
  GitHub Actions only verifies those assets and deploys the extracted static
  tree to Pages; it never performs a full Lean build.
- GitHub Pages receives only a site that satisfies its hosting limits. A full
  bundle that exceeds those limits remains a valid release artifact for the
  future self-hosted service, but it is not dispatched to Pages.
- The same verified bundle is the deployment boundary for the future
  self-hosted service. Hosting adapters must not change bundle contents.

## Alternatives considered

### Build every branch in GitHub Actions

Rejected because documentation builds are long and memory-heavy, GitHub cache
keys are not the authoritative branch cache, and a partial matrix can produce
an incomplete site unless every stage is fail-closed.

### Publish the latest version of every duplicate project implicitly

Rejected because “latest” can change routing without an explicit review. A
canonical mapping makes the public URL stable and auditable.

### Commit generated site output

Rejected because the generated tree is large and reproducible release output,
not source. Release assets provide immutable storage without polluting Git
history.

## Consequences

- Publishing requires successful results for every required branch and project.
- A release tag and its assets are immutable. Republish is allowed only when
  all existing asset digests match exactly.
- Rollback redeploys a previous verified release tag; it does not rebuild or
  overwrite an old release.
- A Pages candidate must be checked independently from the compressed Release
  asset: the published tree must stay below GitHub Pages' 1 GB limit and its
  deployment must finish within 10 minutes. Compression does not relax the
  published-tree limit.
- Changes to release tooling require normal code review and CI before a new
  release is generated.
