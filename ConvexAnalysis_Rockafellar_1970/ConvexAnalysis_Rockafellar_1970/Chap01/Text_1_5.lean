import ConvexAnalysis_Rockafellar_1970.Chap01.AffineDimension

-- Declarations for this item will be appended below by the statement pipeline.

/-
Source/core/bridge triage:
- `source-facing`: Text 1.5 introduces the textbook affine-subspace predicates `point`, `line`,
  `plane`, and `hyperplane`.
- `core/canonical`: the ambient owner abstraction is `AffineSubspace`, with textbook predicates
  already owned upstream as `AffineSubspace.is_point`, `AffineSubspace.is_line`,
  `AffineSubspace.is_plane`, and `AffineSubspace.is_hyperplane`.
- `bridge/view`: no extra bridge is needed here; this item is an owner recall, not a wrapper layer.
- Primitive data vs derived API: `AffineSubspace.affineDim` is the owner-level primitive data, and
  the four predicates in this text are already its chapter-owned derived API.
- Domain-style sampling used here: `AffineSubspace.affineDim`, `AffineSubspace.is_point`,
  `AffineSubspace.is_line`, `AffineSubspace.is_plane`, and `AffineSubspace.is_hyperplane` from
  `AffineDimension`.
- Canonicalization checks:
  - codomain/ambient: this item is predicate-only on `AffineSubspace`; no over-concrete codomain.
  - scalar/structure: inherited owners are over generic `DivisionRing` affine spaces; the
    hyperplane owner is stated directly as codimension-one via
    `Module.finrank 𝕜 (V ⧸ s.direction) = 1`, with no ambient `[FiniteDimensional 𝕜 V]`.
  - owner choice: keep `AffineSubspace` predicates; no concrete model owner appears here.
  - topology layer: no ambient/intrinsic topology surface in this item.
  - notation: no extra notation layer is needed; object-prefix owner predicates already expose the
    textbook surface cleanly.
  - wrapper check: avoid local `Iff.rfl` restatements when no new owner/bridge is introduced.
-/
/- Text 1.5: the textbook affine-subspace predicates are already the canonical chapter owners,
so this item recalls them directly rather than restating definitional `Iff.rfl` wrappers. -/
recall AffineSubspace.is_point
recall AffineSubspace.is_line
recall AffineSubspace.is_plane
recall AffineSubspace.is_hyperplane
