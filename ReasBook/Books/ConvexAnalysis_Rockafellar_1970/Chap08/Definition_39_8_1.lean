import ConvexAnalysis_Rockafellar_1970.Chap01.Defintion_4_8_1
import ConvexAnalysis_Rockafellar_1970.Chap08.Definition_38_5_2

noncomputable section

open scoped Rockafellar

universe u v w

namespace Set

section

attribute [local instance] Classical.propDecidable

variable {X : Type u} {Y : Type v} {α : Type w}
variable [AddGroup α] [ConditionallyCompleteLattice α]
variable [HasPairing X Y α]

/-- Definition 39.8.1: the pairing inner product of a supremum-oriented set `C` and an
infimum-oriented set `D`, when it exists, is the Chapter 38 function inner product of the
indicator of `C` with the concave indicator of `D`. -/
abbrev innerProduct (C : Set X) (D : Set Y) : WithBotTop α :=
  Function.innerProduct (δ[α](· | C)) (fun y ↦ -(δ[α](y | D)))

/-- Definition 39.8.1: the set inner product of `C` and `D` over `α` exists exactly when the two
textbook extrema agree:
`sup_{x ∈ C} inf_{y ∈ D} ⟪x, y⟫ = inf_{y ∈ D} sup_{x ∈ C} ⟪x, y⟫`. -/
def HasInnerProduct (C : Set X) (D : Set Y) : Prop :=
  C.innerProduct D = ⨅ y ∈ D, ⨆ x ∈ C, (⟪x, y⟫ₚ : WithBotTop α)

/-- The source-facing owner `C.innerProduct D` is the Chapter 36 maximin value
`sup_{x ∈ C} inf_{y ∈ D} ⟪x, y⟫`. -/
@[simp] theorem innerProduct_eq_iSup_iInf_pairing
    (C : Set X) (D : Set Y) :
    C.innerProduct D = ⨆ x ∈ C, ⨅ y ∈ D, (⟪x, y⟫ₚ : WithBotTop α) := by
  sorry

private theorem function_hasInnerProduct_iff
    (C : Set X) (D : Set Y) (hCD : C.Nonempty ∨ D.Nonempty) :
    Function.HasInnerProduct (δ[α](· | C)) (fun y ↦ -(δ[α](y | D))) ↔
      C.innerProduct D = ⨅ y ∈ D, ⨆ x ∈ C, (⟪x, y⟫ₚ : WithBotTop α) := by
  sorry

/-- The existence of the set inner product is exactly equality between the two textbook extrema
from Definition 39.8.1. -/
@[simp] theorem hasInnerProduct_iff
    (C : Set X) (D : Set Y) :
    HasInnerProduct (α := α) C D ↔
      C.innerProduct D = ⨅ y ∈ D, ⨆ x ∈ C, (⟪x, y⟫ₚ : WithBotTop α) := by
  rfl

/-- Bridge to the Chapter 38 owner layer: the set-level existence predicate from Definition 39.8.1
is equivalent to saying at least one set is nonempty and the corresponding indicator-function
pairing has a Chapter 38 inner product. -/
theorem hasInnerProduct_iff_nonempty_or_and_functionHasInnerProduct
    (C : Set X) (D : Set Y) :
    HasInnerProduct (α := α) C D ↔
      (C.Nonempty ∨ D.Nonempty) ∧
        Function.HasInnerProduct (δ[α](· | C)) (fun y ↦ -(δ[α](y | D))) := by
  constructor
  · intro hpair
    have hCD : C.Nonempty ∨ D.Nonempty := by
      by_contra hCD
      have hC_empty : C = ∅ := Set.not_nonempty_iff_eq_empty.mp (fun hC ↦ hCD (Or.inl hC))
      have hD_empty : D = ∅ := Set.not_nonempty_iff_eq_empty.mp (fun hD ↦ hCD (Or.inr hD))
      subst C D
      simp at hpair
    exact ⟨hCD, (function_hasInnerProduct_iff C D hCD).2 hpair⟩
  · rintro ⟨hCD, hfun⟩
    exact (function_hasInnerProduct_iff C D hCD).1 hfun

/-- When the set inner product exists, the source maximin value also equals the companion minimax
value `inf_{y ∈ D} sup_{x ∈ C} ⟪x, y⟫`. -/
theorem innerProduct_eq_iInf_iSup_pairing
    {C : Set X} {D : Set Y} (h : HasInnerProduct (α := α) C D) :
    C.innerProduct D = ⨅ y ∈ D, ⨆ x ∈ C, (⟪x, y⟫ₚ : WithBotTop α) := h

end

end Set
