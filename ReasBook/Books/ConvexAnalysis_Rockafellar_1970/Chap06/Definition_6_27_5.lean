import Mathlib.Tactic.Recall
import ConvexAnalysis_Rockafellar_1970.Chap02.ParaboloidEpigraph

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

section Ordered

variable {𝕜 : Type*} [LE 𝕜] [Pow 𝕜 ℕ]

/-!
Source/core/bridge triage:

- `source-facing`: Definition 6.27.5 names the concrete set
  `P = {(ξ₁, ξ₂) | ξ₂ ≥ ξ₁²}` from the Section 27 example.
- `core/canonical`: this set is already owned upstream as
  `paraboloidEpigraph : Set (𝕜 × 𝕜)` in `Chap02/ParaboloidEpigraph`.
- `bridge/view`: the coordinate inequality `ξ₁² ≤ ξ₂` is the canonical set-of/membership view
  already provided by upstream owner API (`paraboloidEpigraph_eq_setOf_sq_le`,
  `mem_paraboloidEpigraph_iff`).

Primitive data vs derived API:
- primitive public data: the canonical owner `paraboloidEpigraph : Set (𝕜 × 𝕜)`;
- derived API: this file keeps only source-level recall/use of the upstream owner and bridge
  theorems, without introducing a parallel local alias.

Domain-style sampling used here:
- the shared source owner `paraboloidEpigraph`.

Layer target: `source-facing` recall at the canonical owner layer.
-/

/- Definition 6.27.5: the source set `P = {(ξ₁, ξ₂) | ξ₂ ≥ ξ₁²}` is already the shared owner
`paraboloidEpigraph`. -/
recall paraboloidEpigraph

/- Source-facing coordinate/set presentation of the same owner. -/
recall paraboloidEpigraph_eq_setOf_sq_le

/- Pointwise membership view of Definition 6.27.5. -/
recall mem_paraboloidEpigraph_iff

end Ordered
