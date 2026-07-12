import Mathlib.Tactic.Recall
import ConvexAnalysis_Rockafellar_1970.Chap06.Definition_6_30_5

/-!
Source/core/bridge triage:

- `source-facing`: the Chapter 6 item at `6.30.5` is the concave-side subdifferential notion and
  its pointwise affine-majorant membership criterion.
- `core/canonical`: the owner abstraction for subdifferentials in this chapter is already
  `_root_.subdifferentialAt` from Chapter 23; on the concave side this is exposed by
  `_root_.concaveSubdifferentialAt`, on the canonical extended codomain layer `WithTopBot`.
- `bridge/view`: `Definition_6_30_5` also provides stronger-model bridge views (`StrongDual` and
  inner-product transport), but this source-facing theorem file keeps the intrinsic pairing layer
  as primary.

Domain-style sampling:
- `_root_.subdifferentialAt` and `_root_.mem_subdifferentialAt` from
  `Chap05.Definition_23_0_6`;
- `_root_.concaveSubdifferentialAt` and
  `_root_.mem_concaveSubdifferentialAt_pairing` from
  `Chap06.Definition_6_30_5`.

Primitive data vs derived API:
- primitive owner data for this item already lives in `Definition_6_30_5`;
- the intrinsic source-facing pointwise inequality is
  `_root_.mem_concaveSubdifferentialAt_pairing`; concrete bridge formulations are derived views.

Layer target: `bridge/view`. This theorem-shaped file adds no new mathematics beyond the owner and
its intrinsic membership specification already introduced in `Definition_6_30_5`, so the faithful
refinement is direct recall rather than a parallel wrapper.
-/

/- The concave-side subdifferential at `x` is already owned by the Chapter 6 bridge declaration
`concaveSubdifferentialAt`; this file reuses that owner directly instead of introducing a second
theorem-level alias. -/
recall concaveSubdifferentialAt

/- The source affine-majorant characterization is already the canonical companion theorem
`mem_concaveSubdifferentialAt_pairing` at the intrinsic pairing layer. -/
recall mem_concaveSubdifferentialAt_pairing

/- The canonical sign bridge is exposed directly on notation surfaces
`x⋆ ∈ ∂⁺[Y]g(x) ↔ -x⋆ ∈ ∂[Y](-g)(x)`, avoiding raw `(Y := Y)` owner noise. -/
recall mem_concaveSubdifferentialAt_pairing_iff_neg_mem_subdifferentialAt_neg

/- Owner-level sign bridge at the same canonical notation surface. -/
recall concaveSubdifferentialAt_eq_preimage_neg_subdifferentialAt_neg_pairing
