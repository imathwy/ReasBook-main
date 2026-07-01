import ConvexAnalysis_Rockafellar_1970.Chap01.AffineDimension

-- Declarations for this item will be appended below by the statement pipeline.

/- 
Source/core/bridge triage:
- `source-facing`: Text 1.4 names the dimension of an affine set.
- `core/canonical`: the chapter owner abstraction is `AffineSubspace.affineDim`.
- `bridge/view`: no extra bridge is needed here; the numbered item is already the owner declaration.
- Primitive data vs derived API: the primitive notion is the chapter-owned definition
  `AffineSubspace.affineDim`, so this file should stay a direct recall rather than introducing a
  parallel alias or wrapper.
- Domain-style sampling used here: `AffineSubspace.affineDim` from `AffineDimension`,
  `Set.affineDim` from `Definition_2_4_10`, and the nearby owner-derived predicates
  `AffineSubspace.is_point` and `AffineSubspace.is_hyperplane`, confirming that the affine-set
  dimension notion is already owned upstream by `AffineSubspace`.
- Canonicalization checks:
  - codomain/ambient layer: no over-concrete codomain is exposed; this item only recalls the owner.
  - scalar/ambient structure: the owner is already at the generic `DivisionRing` affine-space layer.
  - owner choice: the notion is intrinsically affine-subspace dimension, so `AffineSubspace` is the
    correct owner.
  - topology phrasing: this item has no topology-facing statement.
  - owner naming: `AffineSubspace.affineDim` is already the chapter's short canonical owner.
  - notation surface: no extra notation layer is needed for this recall-only item.
-/
/- Text 1.4: the textbook dimension convention for an affine set is the canonical chapter owner
declaration `AffineSubspace.affineDim`, namely the finrank of the parallel subspace when the affine
subspace is nonempty and `-1` for the empty affine subspace. -/
recall AffineSubspace.affineDim
