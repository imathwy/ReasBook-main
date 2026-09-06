# ADR-0016: Preserve proof nodes when showing statement edges

## Status

Accepted. Supersedes ADR-0015's reader All-button behavior only.

## Date

2026-09-06

## Context

Filtering to statement edges also removed proof-dependent declarations. Readers
need to inspect statement relationships without losing those declarations.

## Decision

Replace All with Stmt edges. Compute its node neighborhood and depth using the
union of statement and proof/body dependencies; draw only statement edges between
the retained nodes. Nodes with no visible edge stay present. Existing Stmt and
Proof modes retain their respective node-and-edge filtering. Migrate saved All
selections to Stmt edges. Curated maps without typed evidence remain unfiltered.

Proof and Stmt edges share reference geometry built from the bounded typed union
for the selected scope, depth and section. Drawn nodes and edges are filtered
after layout, keeping common nodes fixed even when statement-only nodes exist.
Switching between these two modes preserves the camera. Stmt remains independently
laid out. This applies to Natural and Layered layouts.

## Consequences

Traversal, reference geometry and drawn-edge selection are separate functions.
Layout identity includes reference edges as well as nodes; Natural can reuse its
SVG and update visibility without another Graphviz run. Proof may leave space for
hidden statement-only nodes to preserve positions. No graph artifact or dependency
classification is changed.
