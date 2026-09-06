# ADR-0012: Ship the reader and review platform with ReasBook

## Status

Accepted

The curated-renderer boundary below is updated by
[ADR-0015](0015-bounded-reader-graphs-and-display-normalization.md); the original
artifacts remain immutable and separately accessible.

## Date

2026-09-06

## Context

The reviewer previously lived in a sibling `Review` checkout with its own catalog
and deployment assumptions. Moving its directory alone would leave relative
imports, authentication paths, generated indexes and release manifests pointing
at different roots. The prototype also rewrote a generated graph renderer with
Python string substitutions, coupling its behavior to specific JavaScript text.

The platform must ship with ReasBook so a checkout can serve the collection and
accept authenticated review comments. Existing release caches are expensive to
rebuild, while existing review records are user data that cannot be reconstructed
by compiling Lean. These two kinds of state need independent deployment and
backup boundaries.

## Decision

- Place the source application at `apps/reasbook-reviewer/`. Its flat HTTP,
  storage, catalog and artifact modules remain small adapters around existing
  SDK capabilities. `bootstrap.py` exposes the checked-out SDK source packages;
  the application is deployed together with that source tree and its frontend,
  not packaged as a wheel that omits static resources.
- Use the deploy SDK's cache defaults, environment parser and reviewer build
  adapters. Store indexes and compatible graph caches under
  `CACHE/reviewer/data`, and SQLite under `CACHE/reviewer/state`. Retain explicit
  path overrides for operators with separate data volumes.
- Read existing release artifacts without modifying or copying their trees at
  application startup. Existing manifests can contain absolute paths, so the
  container deployment mounts the cache at its original absolute path. References
  outside that mount require their own preserved source mounts.
- Mount evidence read-only and review state writable. Run a single application
  worker using the existing SQLite transaction and revision contract. Deployments
  that require horizontal writers need a separate database design decision.
- Serve generic theorem maps with the canonical renderer assets maintained by
  the theorem-graph SDK. Remove the duplicate Python JavaScript string rewriter.
  Curated project renderers remain separate artifacts and are served unchanged.
- Keep statement/proof dependency provenance and incomplete-coverage semantics
  from ADR-0010. Integration does not infer additional dependency edges or claim
  that cached partial graphs are complete.
- Make reading public by default; preserve the artifact-access override. Delegate
  login, OAuth and CSRF to an optional installed ReasLab auth package. Missing
  authentication permits reading but never anonymous writes. Secrets are runtime
  configuration and are excluded from source and image build contexts.
- Preserve one current review per `(book_slug, item_key, actor_id)` plus its
  append-only audit events. This migration does not introduce threaded discussion
  or carry an accepted decision automatically onto changed mathematical content.
  Public history omits transport metadata; administrator exports retain the
  audit record.
- Provide a dedicated reviewer Compose deployment and lightweight GitHub checks.
  Static GitHub Pages publication stays in the existing release workflow because
  it cannot run the comment API. Server startup and reviewer CI never compile Lean.

## Alternatives considered

### Retain a separately deployed sibling repository

Rejected because the application depends on ReasBook catalog, artifact and SDK
contracts. A second checkout adds synchronization and path configuration without
providing an independent product boundary.

### Copy SDK helpers and generated artifacts into the application

Rejected because it creates parallel implementations and hides the provenance of
source, Docs and graph evidence. Cache reuse should preserve release identity.

### Rewrite the backend and discussion schema during relocation

Rejected because review keys, revisions and stored user comments already have a
working contract. Separating persistence from HTTP enables later changes without
coupling the directory migration to a new authentication or discussion model.

## Consequences

- One ReasBook checkout provides the reader and the tools that produce its input.
- Existing caches and review records remain reusable with explicit state mounts.
- A clean checkout can start in read-only mode without the sibling auth project;
  publishing comments still requires provider registration and an installed auth
  implementation.
- Canonical graph behavior is tested in the SDK rather than patched at request
  time. Previously curated renderers retain their own compatibility boundary.
- SQLite backups, OAuth settings and public ingress remain operator-owned. A
  source/image rollback must preserve newer comments and account for any future
  schema migration before restoring older state.
