# ADR-0015: Bound reader graph layouts and normalize comment notation

## Status

Accepted. Updates ADR-0012's curated-renderer compatibility boundary only.

The reader All-button behavior below is superseded by
[ADR-0016](0016-preserve-proof-nodes-in-statement-edge-view.md).

## Date

2026-09-06

## Context

Rendering an entire large dependency graph before hiding distant nodes still
incurs the expensive layout. Curated maps also need the same reader controls
without rewriting JavaScript inside immutable release artifacts. Meanwhile Lean
doc comments mix prose, mathematical notation and program snippets; directly
passing all backticks to TeX loses grouping and source-editor line wraps can
incorrectly become display paragraphs.

## Decision

- Start with a three-hop neighborhood in the existing natural layout. Traverse
  upstream and downstream separately, then pass only that subset to layout.
  Apply the Stmt/Proof relation filter before traversal and layout, so depth and
  nodes follow only matching edges. All retains unclassified links too. Full
  graph includes every matching relationship (plus the selected anchor even when
  isolated); its layer selector is disabled.
- Reuse the SDK renderer for both generic graph JSON and curated data already
  validated by the resolver. The curated JSON endpoint retains curated provenance;
  it does not invent statement/proof classifications. Preserve original assets
  read-only under `evidence/graph/original/`, including relative resource paths.
- Keep comment conversion deterministic and confined to presentation: preserve
  paragraphs and original source, normalize scripts/operators in marked math,
  preserve existing TeX, and escape program snippets as code. Do not reinterpret
  arbitrary prose as mathematics or execute Markdown/HTML from comments.
- Maintain an explicit multi-subject catalog mapping for the current collection,
  independent of Books/Papers and Ready/Pending filters. Unknown resources remain
  visible under General until classified.

## Consequences

Normal graph browsing avoids a full layout, but explicit Full graph can still be
slow, and a high-degree three-hop neighborhood can still contain many nodes.
The node/edge counts expose the displayed subset. Existing partial dependency
coverage remains partial; display depth does not repair missing compiled evidence.
Curated graph data is unchanged, but the embedded controls now share the SDK
renderer; the original presentation remains accessible through its separate route.

Comment normalization is not a complete Lean or Markdown parser. View source and
Copy source preserve the exact indexed statement for comparison. JavaScript unit
tests and browser MathJax checks cover script grouping, paragraphs, code escaping
and the Analysis II subsequence/Cauchy–Schwarz examples.
