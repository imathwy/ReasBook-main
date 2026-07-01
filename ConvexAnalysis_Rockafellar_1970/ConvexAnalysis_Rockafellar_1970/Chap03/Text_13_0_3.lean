import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap01.Definition_2_0_3
import ConvexAnalysis_Rockafellar_1970.Chap01.Defintion_4_8_2

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped Rockafellar

variable {X : Type*} {Y : Type*} {α : Type*}
variable [ConditionallyCompleteLattice α]
variable [HasPairing X Y α]

-- Canonical swapped pairing view used by support-function owners on the dual side.
local instance instHasPairingYX : HasPairing Y X α :=
  HasPairing.swap (X := X) (Y := Y) (L := α)

/-
Source/core/bridge triage:
- `source-facing`: Text 13.0.3 characterizes when a set is contained in a closed half-space
  defined by one evaluation functional.
- `core/canonical`: the owner abstractions are the chapter half-space
  `closedHalfSpaceLE xStar β`
  and the project support function `supportFunction C xStar`.
- `bridge/view`: the textbook inequality `β ≥ δ*(xStar | C)` is rendered through
  `δᵛ[WithTopBot α](xStar | C) ≤ β`, while the set inclusion side remains the chapter half-space
  owner.
- Primitive data vs derived API: this item is a direct theorem about existing owners. Convexity is
  not part of the primitive data for this equivalence.
- Domain-style sampling used here: `supportFunction`, `supportFunction_def`, `closedHalfSpaceLE`,
  and `mem_closedHalfSpaceLE_iff`.
- Layer target: `bridge/view`, at the pairing layer with support-function values in the chapter's
  extended codomain `WithTopBot α`.
-/

-- Proof sketch: unfold `supportFunction C xStar` as the supremum of the values `⟪xStar, x⟫` for
-- `x ∈ C`. Under the canonical swapped pairing instance this is exactly `⟪x, xStar⟫`, so each
-- pointwise half-space bound compares directly with the support supremum.
/-- Text 13.0.3 at the canonical extended-codomain layer: containment in the closed half-space cut
out at level `β : WithTopBot α` is equivalent
to the support-function bound `δᵛ(xStar | C) ≤ β`. -/
theorem subset_closedHalfSpaceLE_withTopBot_iff_supportFunction_le
    (C : Set X) (xStar : Y) (β : WithTopBot α) :
    C ⊆ closedHalfSpaceLE xStar β ↔ δᵛ(xStar | C) ≤ β := by
  rw [supportFunction_def]
  constructor
  · intro h
    refine iSup_le fun x : C ↦ ?_
    change (⟪(x : X), xStar⟫ₚ : WithTopBot α) ≤ β
    exact (mem_closedHalfSpaceLE_iff (X := X)).mp (h x.2)
  · intro h y hyC
    rw [mem_closedHalfSpaceLE_iff (X := X)]
    change (⟪xStar, y⟫ₚ : WithTopBot α) ≤ β
    exact (le_iSup (fun z : C ↦ (⟪xStar, (z : X)⟫ₚ : WithTopBot α)) ⟨y, hyC⟩).trans h

/-- Text 13.0.3, canonical threshold specialization in `WithTopBot α`: for `β : α`, a set `C` is
contained in `{x | ⟪x, xStar⟫ₚ ≤ β}` iff `δᵛ(xStar | C) ≤ (β : WithTopBot α)`. -/
theorem subset_closedHalfSpaceLE_iff_supportFunction_le_withTopBot
    (C : Set X) (xStar : Y) (β : α) :
    C ⊆ closedHalfSpaceLE xStar β ↔ δᵛ(xStar | C) ≤ (β : WithTopBot α) := by
  constructor
  · intro h
    exact
      (subset_closedHalfSpaceLE_withTopBot_iff_supportFunction_le
        C xStar (β : WithTopBot α)).1 <|
        by
          intro x hx
          have hx' : (⟪x, xStar⟫ₚ : α) ≤ β :=
            (mem_closedHalfSpaceLE_iff (X := X)).mp (h hx)
          change ((⟪x, xStar⟫ₚ : WithTopBot α) ≤ (β : WithTopBot α))
          exact
            (WithTop.coe_le_coe).2 <|
              (WithBot.coe_le_coe).2 hx'
  · intro h
    have hWithTop :
        C ⊆ closedHalfSpaceLE xStar (β : WithTopBot α) :=
      (subset_closedHalfSpaceLE_withTopBot_iff_supportFunction_le
        C xStar (β : WithTopBot α)).2 h
    intro x hx
    have hxWithTop : (⟪x, xStar⟫ₚ : WithTopBot α) ≤ (β : WithTopBot α) :=
      (mem_closedHalfSpaceLE_iff (X := X)).mp (hWithTop hx)
    have hxWithBot : ((⟪x, xStar⟫ₚ : α) : WithBot α) ≤ (β : WithBot α) :=
      (WithTop.coe_le_coe).1 hxWithTop
    have hx' : (⟪x, xStar⟫ₚ : α) ≤ β :=
      (WithBot.coe_le_coe).1 hxWithBot
    exact (mem_closedHalfSpaceLE_iff (X := X)).2 hx'

/-- Text 13.0.3, source-facing threshold specialization at the canonical owner layer: for
`β : α`, a set `C` is contained in the closed half-space `{x | ⟪x, xStar⟫ₚ ≤ β}` if and only if
`δᵛ(xStar | C) ≤ β`, equivalently `β ≥ δ*(xStar | C)` in source notation. -/
theorem subset_closedHalfSpaceLE_iff_supportFunction_le
    (C : Set X) (xStar : Y) (β : α) :
    C ⊆ closedHalfSpaceLE xStar β ↔ δᵛ(xStar | C) ≤ (β : WithTopBot α) := by
  simpa using
    (subset_closedHalfSpaceLE_iff_supportFunction_le_withTopBot C xStar β)

end
