# ADR-0003: Pin project source links and checkpoint documentation analysis

## Status

Accepted

## Date

2026-09-04

## Context

Lean documentation strings can contain links to local `.lean` files. When an
`.olean` was built in a different checkout, doc-gen may render those absolute
paths as apparently local static-site links. The files do not belong in the
site, so strict link closure correctly rejects the output. Treating every
missing `.lean` link as valid, however, could publish links to the wrong book
when filenames overlap or conceal stale compiled inputs.

Modern doc-gen also separates analysis from HTML rendering. Analysis is the
expensive phase: a multi-batch branch build may finish every analyzer process
and then fail while rendering or checking links. Keeping only the final
validated site-cache writer transaction makes that safe, but forces an
unnecessary full analysis retry.

## Decision

- A missing local `.lean` link is normalized only when its decoded path occurs
  in the current referring source and has one unique longest suffix match in
  the selected reachable source closure. Exact selected-root ownership may
  disambiguate otherwise equal matches.
- Link spans come from a quote-aware start-tag attribute lexer and must agree
  exactly with the HTML parser's ordered attributes, including duplicates.
  Text resembling `href=` inside another quoted attribute is never edited;
  malformed references that cannot be mapped to one exact span are rejected.
- Generated documentation does not require a base URL. A single empty
  `<base>` has no effect, while any non-empty, repeated, or ambiguous base
  element is rejected so it cannot redirect local link-closure checks to an
  external origin.
- The normalized URL uses the configured GitHub repository and full
  40-hex-character commit SHA. Repository input must be exactly an HTTPS
  `github.com` URL with
  one allowlisted owner segment and one allowlisted repository segment; URL
  credentials, ports, extra path components, encoded delimiters, query, and
  fragment are rejected before an href is emitted. Unknown, ambiguous,
  queried, or unowned source links remain errors.
  Backslash, NUL, `file:` URLs, raw or decoded Windows drive-absolute paths,
  protocol-relative URLs, and protocols outside the explicit
  `http`/`https`/`data`/`mailto` allowlist are unsafe. Missing non-HTML assets
  retain the same fail-closed behavior; external HTML dependencies alone may
  use explicit local stubs. A non-empty regular `style.css` must already exist,
  and a second no-write closure pass validates both generated stubs and edited
  pages.
- An output path is inspected lexically with `lstat` before canonicalization.
  The output itself and every existing parent component must not be a symlink;
  the check is repeated after missing parents are created. This prevents a
  pre-positioned link from redirecting the writer outside its selected root.
- The source-link policy is part of the final documentation-cache identity.
  A cache created immediately before this identity field was introduced may be
  migrated only when every other identity field is equal. Migration validates
  and normalizes an isolated copy, then publishes it through a same-filesystem
  cache-writer transaction under the output lock. Each rename is atomic, and
  rollback preserves the preceding cache on publication failure; the two-rename
  transaction does not promise a lock-free reader a global snapshot.
- Modern doc-gen's completed analyzer database is a separate, hidden,
  content-addressed derived cache. Its identity binds the toolchain, immutable
  revision, Lake manifest, reachable modules and source hashes, batch policy,
  doc-gen executable, analyzer adapter, and compiled inputs. Reachable project
  `.olean` files, project native libraries, doc-gen/leansqlite compiled support,
  the doc-gen executable, and loaded native libraries are content-hashed. When
  the Lake tree has no managed-cache marker, every dependency `.olean`, `.so`,
  and `.a` is also content-hashed.
- A managed branch cache deliberately replaces the full dependency-tree hash
  with its validated cache identity. A `cache-metadata.json` inside an ordinary
  `.lake` directory is never a trust signal. Opt-in requires `.lake` itself to
  be a symlink to a real `lake/branch-...` namespace whose exact directory name
  agrees with an exact schema-1 branch metadata object. Branch, 40-character
  commit, Lake-manifest digest, checked-out `lean-toolchain`, host architecture,
  and namespace key must all agree. The exact field set plus the `branch-`
  namespace establishes the branch-build purpose; metadata for a web cache or
  another purpose is rejected. This structural opt-in is the
  operator-controlled trust boundary, not cryptographic provenance: the shared
  cache must be immutable derived data and operators must replace it as a unit,
  never modify artifacts in place. Reachable project artifacts and analyzer
  support are still hashed from their actual bytes on every lookup.
- A checkpoint is accepted only when its marker and database are the only
  entries, its byte count and digest agree, SQLite integrity succeeds, its
  module set is exact, source URLs are still unset, all analyzer-required tables
  exist, `schema_meta` contains the analyzer's DDL/type hashes, and a canonical
  SQLite-schema fingerprint agrees with the marker. SQLite's backup API creates
  a standalone snapshot so write-ahead-log state cannot be lost.
- Rendering and link validation always happen in a fresh final-site stage.
  A checkpoint can avoid reanalysis but can never be served, packaged, or
  interpreted as a successful documentation build. If a validated restored
  checkpoint fails later rendering or closure, the builder discards the
  isolated output and retries fresh analysis exactly once. It replaces the old
  checkpoint only after that fresh render and closure succeed; a second failure
  is final and leaves the old checkpoint untouched.

## Alternatives considered

### Allow every missing `.lean` link

Rejected because a suffix such as `Chap04/Shared.lean` can exist in several
books, and arbitrary local paths are not immutable release evidence.

### Rewrite links by filename alone

Rejected because it neither proves that the link came from the current source
nor distinguishes stale `.olean` documentation from an intended current link.

### Preserve the failed final-stage directory

Rejected because a directory containing incomplete HTML looks too much like a
publishable site. The analyzer database has a smaller, independently
verifiable contract and is kept under a distinct hidden profile instead.

### Cache rendered pages before link validation

Rejected because link policy is part of the release contract. Only a fully
validated tree may enter the final documentation cache.

## Consequences

- Generated source links are stable across local, SiFlow, GitHub Pages, and
  self-hosted paths and remain bound to the exact release commit.
- A source rename, source or reachable compiled-artifact content change,
  dependency-manifest change, toolchain change, or analyzer change invalidates
  the checkpoint deterministically within the managed-cache trust boundary.
- Render/link failures can be retried without repeating successful analysis,
  while failures never expose a partial site.
- The hidden analysis cache consumes additional disk and may be removed at any
  time to force reanalysis; it is not release data.
