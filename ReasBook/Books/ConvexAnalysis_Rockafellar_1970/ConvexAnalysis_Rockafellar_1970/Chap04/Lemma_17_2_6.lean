import Mathlib
import Mathlib.Tactic.Recall
import ConvexAnalysis_Rockafellar_1970.Chap03.Text_13_0_3

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Rockafellar

/-
Source/core/bridge triage:
- `source-facing`: Lemma 17.2.6 states the half-space containment criterion
  `H ⊇ C ↔ μStar ≥ δ*(xStar | C)` for the half-space cut out by `⟪x, xStar⟫ ≤ μStar`.
- `core/canonical`: the owner declarations are the chapter half-space
  `closedHalfSpaceLE xStar μStar`
  and the project support function `supportFunction C xStar`.
- `bridge/view`: the source notation `δ*(xStar | C)` is exactly
  `supportFunction C xStar`, and the source inclusion `H ⊇ C` is the same set-theoretic relation
  as `C ⊆ closedHalfSpaceLE xStar μStar`.
- Primitive data vs derived API: this item introduces no new data or local wrapper; it is direct
  reuse of the owner theorem already proved in Chapter 13.
- Domain-style sampling used here: `closedHalfSpaceLE`, `supportFunction`,
  `subset_closedHalfSpaceLE_withTopBot_iff_supportFunction_le`, and
  `subset_closedHalfSpaceLE_iff_supportFunction_le_withTopBot`.
- Layer target: `bridge/view`; keep the canonical owner theorem as a recall and add the textbook
  `H ⊇ C` surface as a thin orientation bridge at the intrinsic threshold layer
  `β : WithTopBot α`.
- The source side condition `xStar ≠ 0` is redundant for this equivalence itself, so it is not
  kept in the public interface.
-/
/- Lemma 17.2.6: if `H = closedHalfSpaceLE xStar μStar`, then `H ⊇ C` if and only if
`μStar ≥ supportFunction C xStar`. This is exactly
`subset_closedHalfSpaceLE_withTopBot_iff_supportFunction_le`. -/
recall subset_closedHalfSpaceLE_withTopBot_iff_supportFunction_le
recall subset_closedHalfSpaceLE_iff_supportFunction_le_withTopBot

section

universe u v w

variable {X : Type u} {Y : Type v} {α : Type w}
variable [ConditionallyCompleteLattice α]
variable [HasPairing X Y α]

-- Canonical swapped pairing view needed by `δᵛ(xStar | C)` when `xStar : Y` and `C : Set X`.
local instance : HasPairing Y X α :=
  HasPairing.swap (X := X) (Y := Y) (L := α)

/-- Textbook inequality orientation of Lemma 17.2.6:
`H ⊇ C ↔ β ≥ δ*(x* | C)` at the intrinsic threshold layer `β : WithTopBot α`. -/
theorem closedHalfSpaceLE_superset_iff_ge_supportFunction
    (C : Set X) (xStar : Y) (β : WithTopBot α) :
    closedHalfSpaceLE xStar β ⊇ C ↔ β ≥ δᵛ(xStar | C) := by
  simpa [ge_iff_le] using
    (subset_closedHalfSpaceLE_withTopBot_iff_supportFunction_le C xStar β)

end
