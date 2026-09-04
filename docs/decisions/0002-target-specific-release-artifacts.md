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
  its compatibility path. Legacy native MD4Lean libraries are resolved from
  built artifacts and loaded in dependency order, rather than inferred from a
  Lean version. The isolated, content-addressed cache profile is
  `project-modules-v2`, so source, toolchain, target, module, doc-gen, or batch
  policy changes cannot silently reuse incompatible output.
- Packaging derives two immutable artifacts from the verified aggregate site:
  `full` retains every assembled project version; `pages` retains the public
  catalog and explicit canonical project versions. Both retain reachable
  project-module docs, Verso pages, theorem maps, and dependency stubs.
- Every theorem map, whether generated or curated, carries a generated release
  context that matches its project specification. Repository source links are
  pinned to the full project commit; the branch name remains display metadata
  only. Finalization rejects missing or stale identities before packaging.
- A `ReleaseSet` binds both artifact names, bundle SHA-256 values, site-tree
  SHA-256 values, file counts, byte counts, and the artifact-policy digest to
  the same `ReleaseSpec`.
- GitHub Releases carry the Pages bundle, its manifest and checksum, and the
  `ReleaseSet`. Before upload, the local publisher verifies the policy digest
  and both artifact records. The publish-only workflow independently verifies
  the Pages archive and its available ReleaseSet bindings before deploying; it
  never builds Lean or documentation and does not receive the full archive.
- GitHub publication is allowed only when repository immutable releases are
  enabled. The one-time configuration command audits and enables that setting
  with an administrator-authorized token. The publisher waits for the Release
  REST record to become immutable before dispatch, while the workflow uses
  GitHub's Release and per-asset verification commands because its scoped
  workflow token cannot inspect repository administration settings.
- Creating a new Release tag requires a clean local checkout at the current
  GitHub default-branch commit, and that commit must be the ReleaseSpec's exact
  `source.registry_commit`. A dirty tooling revision remains useful for local
  canaries, but is not publishable: GitHub requires the exact clean
  `COMMIT+tooling-sha256:DIGEST` form. The publisher creates the Git ref before
  the draft Release, creates and publishes the draft through stable REST APIs,
  accepts a pre-existing or concurrently created ref only when its fully
  dereferenced target is exact, and rechecks it before upload, publication, and
  dispatch. Wait-mode run discovery also uses the Actions REST API so the
  release path does not depend on version-specific GitHub CLI JSON fields.
  Re-dispatching an existing tag requires the same target and revalidates every
  remote asset digest. The publish-only workflow independently repeats both
  the tag equality and clean-tooling checks after dereferencing a lightweight
  or annotated tag.
- The Pages profile fails closed above 850 MB of extracted content, 60,000
  files, or 950 MB compressed. Archive member count and expanded bytes are
  checked from the tar listing before extraction. Hidden files are uploaded and
  included in the site-tree digest, except exact `.git` and `.github` path
  segments, which are rejected because GitHub always omits them. These are
  operational margins below GitHub's hard limits, not targets to fill.
- Self-hosted deployment accepts only the `full` artifact. It installs into a
  versioned directory, exposes the configured base path below `public/`, and
  atomically switches a `current` symlink. A failed health check restores the
  preceding link.
- A portable self-hosted install requires the matching `ReleaseSet`, the
  expected bundle SHA-256, and a separately trusted artifact-policy digest.
  The per-release bundle SHA-256 must arrive through an independent
  authenticated channel: neither a co-transferred `SHA256SUMS` nor the
  normally cross-release-stable policy digest authenticates release identity.
  Before extraction it validates archive member types, canonical paths,
  duplicate names, declared file counts and byte totals, and bounded metadata.
  Operators must choose either an HTTP(S) health check or an explicit
  filesystem-only bootstrap check.
- Before publication, one local acceptance command verifies both archive and
  ReleaseSet bindings, projects the Pages route contract, installs the full
  artifact through the production atomic installer, and serves both resulting
  trees. The HTTP pass covers every declared project-version entry; a required
  Playwright pass exercises every route kind at desktop and mobile widths and
  rejects base-path escapes, console/page errors, HTTP failures, and transport
  failures.
- The successful required-browser acceptance record is promotion evidence, not
  advisory output. Both GitHub and direct self-hosted publication rebind its
  release, spec, policy, two archive checksums, site digests, counts, browser
  checks, and atomic-install result to the current package before any target
  mutation. It also records and rechecks the exact bytes of both external
  manifests, both checksum files, and the shared `ReleaseSet`; the GitHub
  publisher compares the external Pages manifest to the archive member before
  upload. Dry-runs apply the same gate. One-click deploy and resume run this
  acceptance gate automatically after packaging.
- ReleaseSpec v1 cannot express the one per-project Verso exception. Acceptance
  therefore reads the existing capability registry only from the exact
  release-scoped tooling snapshot named by `source.tooling_revision`. A local
  checkout is a fallback only when its complete tooling digest matches that
  immutable binding. This preserves old ReleaseSpecs without allowing later
  checkout changes to relax validation.
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
- The Pages workflow recomputes that policy digest from its trusted checkout.
  An older immutable Release cannot be re-dispatched after the default-branch
  policy changes; operators must produce a new ReleaseSpec and acceptance
  record.
- Old schema-version-1 full bundles remain readable; new manifests identify
  their artifact explicitly.
