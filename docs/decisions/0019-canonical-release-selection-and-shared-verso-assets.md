# ADR-0019: Canonical release selection and shared Verso assets

## Status

Accepted

## Context

The May/Forster Pages refresh exceeded the 920 MB operational budget before
publication. The old Pages artifact alone occupied 885,479,760 bytes. An audit
found approximately 74 MB of duplicate plain inline scripts and 12 MB of
duplicate styles in Verso heads. Much of that data is an identical navigation
catalog repeated in hundreds of pages, not mathematical content.

Several old versioned paper readers also contain empty sections. Newer canonical
readers are available in verified caches; retaining an empty historic reader in
a new release is not a useful substitute for the archived original release.

## Decision

- Add explicit `selection.mode: canonical` alongside the backward-compatible
  `all_active` mode. It selects one configured canonical occurrence per project.
  This is independent of `site.include_historical_versions`, which remains true
  in the Pages profile to preserve `/versions/<version>/` URL prefixes.
- Both delivery artifacts describe the same selected ProjectSpecs. `full` keeps
  the full content of that selection; previous immutable releases and caches
  remain available. This does not relabel newer Lean artifacts as old versions.
- Existing historical reading links may redirect to the explicitly canonical
  project, retaining a matching deep suffix where possible. The redirect clearly
  states that it targets the canonical version. Never replace an API page with a
  capacity placeholder simply because it is large.
- Keep existing API namespaces of known selected projects across retained
  branches when doc-gen's navbar/search data refers to them. Canonical reader
  selection must not turn those real API links into 404s or placeholders.
- During Pages projection, share repeated attribute-free classic scripts and
  styles from Verso heads using content-addressed `static/shared-verso/` assets.
  Scripts remain parser-blocking and in their original order. Native Lean HTML,
  prose and anchors in the body are byte-identical; Docs HTML is not rewritten.
- Leave context-sensitive assets inline: CSS relative resources/imports, module
  imports, `document.currentScript`, source maps, CSP pages, templates and
  conditional/noscript content. No global minification or code truncation.
- Reuse separately verified Verso producer caches without replacing existing
  Docs, Source or Graph output. Numeric tooltip databases are namespaced per
  producer. Preserve route aliases emitted by the maintained Pages assembler.
- A chapter index with Docs links is labelled and reported as an index, not as
  newly compiled item-level Verso. Cached compilation status alone is not proof
  of reading content; check visible pages and real navigation before promotion.
- When an indexed item lacks an API page, replace only its generated API link
  with an explicit unavailable label if the adjacent same-module Lean source
  was verified in the pinned Git tree. Keep a commit-qualified source link.
  Never generate a fake API page or suppress unrelated link errors.
- Keep all existing checksum, immutable release, content, browser and capacity
  gates. Selection is explicit in configuration, never an automatic response to
  exceeding the budget.

This refines ADR-0008's selection scope, not its guarantee to retain API pages
owned by every selected ProjectSpec. ADR-0002 still governs artifact binding and
immutable publication. The independently deployed Reviewer and its review data
are unaffected by this static Pages operation.

## Alternatives considered

Deleting proof bodies or selected API documentation was rejected because it
breaks the reader. Raising the budget was rejected because GitHub's 1 GB hard
limit remains. Keeping every historical occurrence remains available through
`all_active`, but is not the default for this public refresh. Removing remote
caches is unnecessary and would discard reusable compilation work.
