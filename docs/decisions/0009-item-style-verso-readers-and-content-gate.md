# ADR-0009: Generate compact Verso readers and reject empty publications

## Status

Accepted

## Date

2026-09-06

## Context

ReasBook projects use more than one source layout.  Most books and papers
expose prose modules named `sectionNN`, which the Verso generator already
recognized.  Some books instead keep one Lean module per formalized item under
a chapter directory, for example `Chap01/Definition_1_1_1.lean`, with
`Book.lean` and `Chap01.lean` serving only as aggregation modules.  Some papers
use the same item-per-module layout directly below the paper directory, for
example `Theorem_2_9.lean`.  A third layout keeps meaningful prose in
`sectionNN_partN.lean` while `sectionNN.lean` contains imports only.

The old discovery rule treated a module as reader content only when its name
looked like a section or its module documentation contained a short heading.
That heuristic rejected the aggregation chapters of *A Concise Course in
Algebraic Topology* and deliberately skipped its item modules.  The resulting
Verso artifact was structurally valid but contained only documentation and
source links plus an empty-directory message.  Route, HTTP, and browser smoke
tests all passed because they did not assert that a required Verso page
contained readable project content.

Rendering every item module as its own Verso page would repair discovery at the
cost of hundreds or thousands of additional literate targets per project,
substantially increasing build time and artifact size.  The API documentation
already provides a detailed page for each item.

## Decision

- Treat chapter aggregation modules such as `Chap01.lean` as structural
  modules independently of prose-title heuristics.
- Recognize a conservative allowlist of item kinds in names of the form
  `Kind_C_<tail>` only when the encoded chapter agrees with the enclosing
  `ChapNN` directory.  Classify the complete chapter inventory before deciding
  whether a reader owns it.  A mixed chapter is item-dominant only when it has
  at least five items and at least four items per ordinary section; a chapter
  with no ordinary sections needs only one item.
- Keep item modules out of the literate-module manifest.  Generate one compact
  Verso chapter reader per non-empty item-style chapter, group its items by
  section, and link each item to its existing API documentation and pinned
  source location.
- Apply the same complete-inventory and dominance rules to item-style papers.
  Their root page links to a compact `papers/<slug>/items/` child reader, so the
  root remains a directory and the item list remains a bounded, independently
  testable content page.  Paper items likewise stay out of the literate-module
  manifest and sidebar.
- When a paper's `sectionNN.lean` contains only imports and has discovered
  `sectionNN_partN.lean` children, publish a generated section index at the
  parent route.  It links the parent API/source and every part's reading page,
  API page, and pinned source.  A parent containing any other Lean command is
  left untouched.
- Publish each compact reader at the canonical
  `books/<slug>/chapters/chapNN/` route.  When an aggregation module previously
  supplied a flat route, retain that route as an alias owned by the same
  generated page.  Duplicate ownership fails generation.
- Include generated book-reader metadata in sidebar data and every generated
  route in project-fragment manifests so independently built fragments remain
  self-describing and safe to merge.  Fine-grained item names do not enter the
  shared sidebar.
- Read a book's display title from the top-level scalar `title` in `book.yml`
  or `book.yaml`, using a dependency-free, non-executing scalar parser and a
  deterministic identifier fallback.
- Replace or remove generated chapter, paper-item, and paper-section pages only
  when they carry that page type's exact ownership marker.  In fragment mode,
  stale cleanup is restricted to the selected project.  A colliding
  hand-maintained page fails generation rather than being overwritten.
- Release acceptance inspects immutable version-qualified Verso roots, not the
  canonical redirect adapter.  A required Verso output fails when it carries a
  known empty marker or has neither a reachable project reading route nor
  explicitly marked standalone content.  It recognizes the supported
  `article`, `main`, and legacy `role="main"` wrappers, validates project-local
  redirect targets and cycles, memoizes the bounded content graph, and ignores
  ordinary backlinks to an ancestor.  A standalone root must carry
  `data-reasbook-verso-standalone="true"` as well as readable prose.  Pages
  separately verifies that each canonical adapter's zero-second refresh and
  anchor target the expected canonical version; the full self-hosted artifact
  checks every included version.

## Alternatives considered

### Render every item module as a Verso page

Rejected because API documentation already provides the declaration-level
view.  Multiplying literate targets by the number of formalized items would
make a navigation fix unnecessarily expensive to build and host.

### Hand-author special pages for the affected projects

Rejected because the layouts are shared by multiple books and papers and
evolve with the Lean source.  Source-derived indices avoid a second manually
maintained inventory.

### Keep route-only release validation

Rejected because an empty generated shell is still a valid HTML file and
returns HTTP 200.  The failure is semantic and must be checked before immutable
publication.

### Require every work to have a child route

Rejected because a deliberately single-page book or paper is valid.  Such a
work may satisfy the content contract with standalone readable prose in its
root page.

## Consequences

- Item-style books and papers expose useful, bounded Verso navigation without
  a declaration-per-page build explosion, and imports-only paper aggregators
  no longer strand their substantive part pages.
- `book.yml` becomes the preferred source for a book's displayed title while
  malformed or structured values remain harmless fallbacks.
- Generator changes affect Verso cache identity and require a new immutable
  release, but existing Lean and API-documentation caches remain reusable.
- A required Verso artifact can no longer be released merely because its root
  exists and returns HTTP 200; intentionally content-free projects must be
  explicitly exempted from Verso in the bound release capabilities.
