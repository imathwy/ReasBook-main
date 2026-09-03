# ADR-0002: Derive target-specific artifacts from one release

## Status

Accepted

## Date

2026-09-04

## Context

The complete ReasBook site contains every version of every project and can grow
beyond GitHub Pages' 1 GB published-site limit. Transitive doc-gen4 API output
also has a high memory peak: measured SiFlow CPU containers provided about
9 GiB and 16 GiB, and both were killed while constructing dependency-wide
indexes. GitHub Pages is a temporary public host, while the long-term target is
a server controlled by the project. Rebuilding or rewriting the site for each
host would make it hard to prove that both deployments came from the same Lean
sources.

A one-paper canary made the size difference concrete: its complete site was
720,629,841 bytes, while a canonical projection with dependency-documentation
stubs was 62,635,534 bytes. The public catalog, project documentation, Verso
pages, and theorem map remained available at their original URLs.

## Decision

- One immutable `ReleaseSpec` continues to identify all source commits,
  toolchains, canonical versions, and required build outputs.
- From each selected entry root, the build SDK follows imports through
  project-owned Lean modules and documents the reachable closure in batches of
  at most 128 modules. Mathlib, Lean, and other external libraries are excluded.
  Referenced external HTML pages are materialized as explicit lightweight
  stubs so navigation is link-closed.
- Modern doc-gen writes and renders a database trimmed to that reachable
  project closure; the legacy adapter renders the same bounded module set via
  its compatibility path. The isolated, content-addressed cache profile is
  `project-modules-v2`, so source, toolchain, target, module, doc-gen, or batch
  policy changes cannot silently reuse incompatible output.
- Packaging derives two immutable artifacts from the verified aggregate site:
  `full` retains every assembled project version; `pages` retains the public
  catalog and explicit canonical project versions. Both retain reachable
  project-module docs, Verso pages, theorem maps, and dependency stubs.
- A `ReleaseSet` binds both artifact names, bundle SHA-256 values, site-tree
  SHA-256 values, file counts, byte counts, and the artifact-policy digest to
  the same `ReleaseSpec`.
- GitHub Releases carry the Pages bundle, its manifest and checksum, and the
  `ReleaseSet`. Before upload, the local publisher verifies the policy digest
  and both artifact records. The publish-only workflow independently verifies
  the Pages archive and its available ReleaseSet bindings before deploying; it
  never builds Lean or documentation and does not receive the full archive.
- Creating a new Release tag requires a clean local checkout at the current
  GitHub default-branch commit. Re-dispatching an existing tag instead trusts
  the already-resolved tag and revalidates every remote asset digest.
- The Pages profile fails closed above 850 MB of extracted content, 60,000
  files, or 950 MB compressed. These are operational margins below GitHub's
  hard limits, not targets to fill.
- Self-hosted deployment accepts only the `full` artifact. It installs into a
  versioned directory, exposes the configured base path below `public/`, and
  atomically switches a `current` symlink. A failed health check restores the
  preceding link.
- A portable self-hosted install requires the matching `ReleaseSet`, the
  expected bundle SHA-256, and a separately trusted artifact-policy digest.
  Before extraction it validates archive member types, canonical paths,
  duplicate names, declared file counts and byte totals, and bounded metadata.
  Operators must choose either an HTTP(S) health check or an explicit
  filesystem-only bootstrap check.
- Both hosts serve the unchanged `/ReasBook/` base path. A self-hosted web
  server uses `<deploy-root>/current/public` as its document root. The
  production container mounts the deploy root rather than the resolved
  `current` target, so it observes later atomic symlink switches without being
  recreated.

This decision supersedes ADR-0001 only where that record calls for one bundle
to serve both hosting targets. Its remote-build, canonical-version, immutable
tag, and no-generated-files-in-Git decisions still apply.

## Alternatives considered

### Publish the complete site to GitHub Pages

Rejected because site size is already close to the hard limit for a single
paper and will not scale to all branches. Compression does not change the
published-tree limit.

### Maintain an independent GitHub-only build

Rejected because it would duplicate expensive work and allow GitHub and the
self-hosted service to drift to different source or tooling revisions.

### Remove every omitted documentation link

Rejected because removing generated links is brittle and turns useful type
references into silent navigation failures. Explicit stubs preserve URL
closure and point readers back to the project documentation, source, and
theorem map.

### Upload the full bundle to every GitHub Release

Rejected as a requirement because large releases can exceed GitHub's
per-asset limit. The full bundle remains portable and verified, but may be
transferred directly to project-owned storage or servers.

## Consequences

- A release is publishable only after both artifacts and the `ReleaseSet`
  verify successfully.
- Pages is intentionally a canonical view, not a complete historical mirror.
- Self-hosted storage must have room for the new release and the currently
  active release during an atomic upgrade.
- Artifact-policy changes create a new release even when the Lean source
  commits are unchanged.
- Old schema-version-1 full bundles remain readable; new manifests identify
  their artifact explicitly.
