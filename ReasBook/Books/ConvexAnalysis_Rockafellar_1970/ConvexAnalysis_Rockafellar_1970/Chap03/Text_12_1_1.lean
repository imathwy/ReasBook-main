import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap01.EOrder.Basic
import ConvexAnalysis_Rockafellar_1970.Chap01.Definition_2_0_3
import ConvexAnalysis_Rockafellar_1970.Chap01.Defintion_4_8_1

-- Declarations for this item will be appended below by the statement pipeline.

section

open scoped Rockafellar

universe u v

variable {X : Type u} {Y : Type v} {𝕜 : Type*}
variable [Preorder 𝕜] [HasPairing X Y 𝕜]

/-!
Source/core/bridge triage for this item.

- `source-facing`: Text 12.1.1 specializes the affine-minorant condition `h ≤ f` to the indicator
  function of a convex set `C` and to the source affine profile `h(x) = ⟪x, y⋆⟫ₚ - β`.
- `core/canonical`: the owner abstractions are the pointwise order on
  `WithBotTop`-valued functions, the chapter indicator bridge `indicatorFunction C`,
  the generic codomain lift `Function.toWithBotTop`, and the half-space
  `closedHalfSpaceLE yStar β`.
- `bridge/view`: the intermediate source wording "`h(x) ≤ 0` for every `x ∈ C`" is kept as a thin
  companion theorem between the function-order statement and the half-space containment statement.

Domain-style sampling used here:
- `indicatorFunction` and `indicator_def` from `Defintion_4_8_1`;
- `Function.toWithBotTop` from `Chap01.EOrder.Basic`;
- `closedHalfSpaceLE` and `mem_closedHalfSpaceLE_iff` from `Definition_2_0_3`;
- the pointwise order on `WithBotTop`-valued functions already used in Chapter 12.

Layer target: `bridge/view`; the public statement keeps the source specialization explicit and
expresses the final conclusion through the canonical half-space containment API.

Although the source states this in `R^n`, the owner declarations used here only need a pairing into
an ordered scalar layer, so the file is kept at that primitive ambient level.
-/

-- Proof sketch: outside `C`, the indicator has value `⊤`, so the inequality is automatic. On `C`,
-- the indicator has value `0`, so pointwise domination is exactly the condition
-- `⟪x, y⋆⟫ₚ - β ≤ 0`.
/-- The affine profile `x ↦ ⟪x, y⋆⟫ₚ - β`, viewed in `WithBotTop 𝕜`, lies below the indicator of
`C` exactly when it is nonpositive on `C`. -/
private theorem affineFunction_le_indicatorFunction_iff_nonpos_on_set
    [Zero 𝕜] [Sub 𝕜]
    (C : Set X) (yStar : Y) (β : 𝕜) :
    (fun x : X ↦ ⟪x, yStar⟫ₚ - β).toWithBotTop ≤ (δ(· | C) : X → WithBotTop 𝕜) ↔
      ∀ x ∈ C, ⟪x, yStar⟫ₚ - β ≤ 0 := by
  constructor
  · intro h x hx
    have hx' : (((⟪x, yStar⟫ₚ - β : 𝕜) : WithBotTop 𝕜)) ≤ 0 := by
      simpa [hx] using h x
    exact WithBotTop.coe_le_coe_iff.mp hx'
  · intro h x
    by_cases hx : x ∈ C
    · have hx' : ⟪x, yStar⟫ₚ - β ≤ 0 := h x hx
      have hx'' : (((⟪x, yStar⟫ₚ - β : 𝕜) : WithBotTop 𝕜)) ≤ 0 := by
        exact WithBotTop.coe_le_coe_iff.mpr hx'
      simpa [hx] using hx''
    · change (((⟪x, yStar⟫ₚ - β : 𝕜) : WithBotTop 𝕜)) ≤ (δ(x | C) : WithBotTop 𝕜)
      rw [indicator_def, if_neg hx]
      exact le_top

-- Proof sketch: first reduce `h ≤ indicatorFunction C` to the condition `⟪x, y⋆⟫ₚ - β ≤ 0` on
-- points of `C`. Then rewrite `⟪x, y⋆⟫ₚ - β ≤ 0` as `⟪x, y⋆⟫ₚ ≤ β` and use
-- `mem_closedHalfSpaceLE_iff` to identify this with `x ∈ closedHalfSpaceLE yStar β`.
variable [AddGroup 𝕜] [AddRightMono 𝕜]

-- Proof sketch: combine the indicator-majorization/nonpositivity bridge with the canonical
-- half-space membership lemma `mem_closedHalfSpaceLE_iff`.
private theorem affineFunction_le_indicatorFunction_iff_subset_closedHalfSpaceLE
    (C : Set X) (yStar : Y) (β : 𝕜) :
    (fun x : X ↦ ⟪x, yStar⟫ₚ - β).toWithBotTop ≤ (δ(· | C) : X → WithBotTop 𝕜) ↔
      C ⊆ closedHalfSpaceLE yStar β := by
  rw [affineFunction_le_indicatorFunction_iff_nonpos_on_set]
  constructor
  · intro h x hx
    rw [mem_closedHalfSpaceLE_iff]
    exact le_of_sub_nonpos (h x hx)
  · intro h x hx
    exact sub_nonpos.mpr (mem_closedHalfSpaceLE_iff.mp (h hx))

/-- Text 12.1.1: a set `C` lies in the closed half-space `{x | ⟪x, y⋆⟫ₚ ≤ β}` exactly when the
affine profile `x ↦ ⟪x, y⋆⟫ₚ - β`, viewed in `WithBotTop 𝕜`, lies below the indicator of `C`. -/
theorem subset_closedHalfSpaceLE_iff_affineFunction_le_indicatorFunction
    (C : Set X) (yStar : Y) (β : 𝕜) :
    C ⊆ closedHalfSpaceLE yStar β ↔
      (fun x : X ↦ ⟪x, yStar⟫ₚ - β).toWithBotTop ≤ (δ(· | C) : X → WithBotTop 𝕜) := by
  exact (affineFunction_le_indicatorFunction_iff_subset_closedHalfSpaceLE (C := C)
    (yStar := yStar) (β := β)).symm

end
