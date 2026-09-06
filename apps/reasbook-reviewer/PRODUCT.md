# Product

<!-- impeccable:product-schema 1 -->

## Platform

web

## Users

Researchers and contributors reviewing Lean formalizations of ReasBook books and papers. They work through many declarations, compare the formal statement with generated documentation and the source text, and record a shared review decision.

## Product Purpose

ReasBook Reviewer turns a book's generated Lean index into a navigable evidence workspace. A reviewer can switch books, inspect a declaration's source, Lean docs, Verso page, and theorem-map context, then save an auditable accepted, mismatch, other, or cleared decision.

## Positioning

The unit of review is a book statement resolved against available release artifacts. Review state is separate from build artifacts and keyed by book, declaration, and reviewer, not by release commit. Regenerating evidence preserves decisions, but does not establish that an earlier decision applies to changed content.

## Operating Context

The service is maintained in `apps/reasbook-reviewer` inside ReasBook and reads immutable release/cache trees produced by the ReasBook build and deploy SDKs. It may be mounted below a path-stripping proxy and uses ReasLab OAuth for write access. Large source, docs, and Verso trees stay outside the application checkout.

## Capabilities and Constraints

- Multiple books and papers are listed in one catalog and can be switched without leaving the workspace.
- Review items prefer theorem-map statements and fall back to a lightweight declaration index when no theorem map exists.
- Evidence is read-only: source snippets, doc-gen HTML, Verso HTML, and theorem-map context are proxied through constrained paths.
- Review writes use optimistic revisions, append-only history, CSRF protection, and per-book isolation.
- Unbuilt artifacts remain explicit pending states; the reviewer never runs Lean or Lake during a browser request.

## Evidence on Hand

The owning ReasBook repository, shared release cache, generated per-book indexes under the configured data root, doc-gen SQLite caches, Verso release sites, and theorem-map JSON are real project evidence. No placeholder declarations or fabricated review claims may be added.

## Product Principles

1. Find the statement before reading the implementation.
2. Expose evidence provenance and require renewed judgment when the underlying release changes.
3. Show the source, docs, Verso narrative, and graph as adjacent evidence, not unrelated links.
4. Make incomplete builds visible without blocking review of ready books.
5. Preserve reviewer drafts and history across book switching and concurrent edits.

## Accessibility & Inclusion

The workspace must support keyboard navigation, visible focus, reduced motion, readable contrast, narrow viewports, and explicit loading, empty, unavailable, conflict, and error states.

## Assumptions

The initial implementation infers that `Operate` is the primary surface mode, that the existing bundle-reviewer is the interaction reference, and that release cache paths are trusted read-only evidence. These assumptions should be revisited if ReasBook changes its release layout.
