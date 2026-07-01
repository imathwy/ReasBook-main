import ConvexAnalysis_Rockafellar_1970.Chap01.Defintion_4_8_1
import ConvexAnalysis_Rockafellar_1970.Chap07.Definition33_0_8

noncomputable section

universe u v w

open scoped Rockafellar

attribute [local instance] Classical.propDecidable

namespace Function

section IndicatorOfPoint

variable {X : Type u} {Y : Type v} {α : Type w}
variable [AddGroup α] [ConditionallyCompleteLattice α] [HasPairing X Y α]

/-!
Source/core/bridge triage:

- `source-facing`: Lemma 33.0.9 evaluates the convex pairing of the indicator of a single point.
- `core/canonical`: the owner layer is the Chapter 1 indicator `δ[α](· | C)` with
  `convexConjugate`; the Chapter 33 convex-pairing notation `⟪f, y⟫ᶠ` is a surface view.
- `bridge/view`: the source point-indicator `δ(· | x)` is rendered canonically as the singleton
  indicator `δ[α](· | ({x}))`; no extra wrapper owner is introduced.

Domain-style sampling used here:
- `indicator` / `δ[α](· | C)` from Chapter 1;
- the branch lemmas `indicator_of_mem` and `indicator_of_notMem`;
- `convexConjugate` / `f⋆` from Chapter 12;
- `convexConjugate_eq_iSup_pairing_sub` as the canonical owner-side evaluation formula.
-/

-- Proof sketch: unfold the conjugate as a supremum of affine defects. For `z = x`, the singleton
-- indicator contributes `0`, giving `⟪x, y⟫ₚ`; for `z ≠ x`, the indicator is `⊤`, so the defect is
-- `⊥`. The supremum therefore collapses to the single surviving value.
/-- Owner-form statement for Lemma33.0.9: the conjugate of the singleton indicator equals the
pairing with the singleton point. -/
theorem convexConjugate_indicator_singleton
    (x : X) (y : Y) :
    (δ[α](· | ({x} : Set X)))⋆ y = ⟪x, y⟫ₚ := by
  rw [convexConjugate_eq_iSup_pairing_sub]
  refine le_antisymm ?_ ?_
  · refine iSup_le ?_
    intro z
    by_cases hz : z = x
    · subst hz
      have hz0 : (δ[α](z | ({z} : Set X)) : WithTopBot α) = 0 := by
        exact indicator_of_mem ({z} : Set X) (by simp)
      rw [hz0, WithBotTop.sub_eq_add_neg, WithBotTop.neg_zero, add_zero]
    · have hz' : z ∉ ({x} : Set X) := by
        simpa [Set.mem_singleton_iff] using hz
      have hzTop : (δ[α](z | ({x} : Set X)) : WithTopBot α) = ⊤ := by
        exact indicator_of_notMem ({x} : Set X) hz'
      rw [hzTop, WithBotTop.sub_top]
      exact bot_le
  · have hle :
        (⟪x, y⟫ₚ - δ[α](x | ({x} : Set X)) : WithTopBot α) ≤
          ⨆ z : X, ⟪z, y⟫ₚ - δ[α](z | ({x} : Set X)) := by
      exact le_iSup (fun z : X ↦ ⟪z, y⟫ₚ - δ[α](z | ({x} : Set X))) x
    have hx0 : (δ[α](x | ({x} : Set X)) : WithTopBot α) = 0 := by
      exact indicator_of_mem ({x} : Set X) (by simp)
    rw [hx0, WithBotTop.sub_eq_add_neg] at hle
    have hle' :
        (⟪x, y⟫ₚ : WithTopBot α) ≤
          ⨆ z : X, ⟪z, y⟫ₚ - δ[α](z | ({x} : Set X)) := by
      simpa [WithBotTop.neg_zero, add_zero] using hle
    exact hle'

/-- Lemma33.0.9: the convex pairing of the indicator of the singleton `{x}` is the pairing with
`x`. -/
theorem convexPairing_indicator_singleton
    (x : X) (y : Y) :
    ⟪(δ[α](· | ({x} : Set X))), y⟫ᶠ = ⟪x, y⟫ₚ := by
  exact convexConjugate_indicator_singleton x y

end IndicatorOfPoint

section NegIndicatorOfPoint

variable {X : Type u} {Y : Type v} {α : Type w}
variable [AddGroup α] [ConditionallyCompleteLattice α] [HasPairing X Y α]

-- Proof sketch: unfold the concave conjugate as the infimum formula for the negative singleton
-- indicator. At `z = x` the value is exactly `⟪x, y⟫ₚ`, while every other point contributes `⊤`,
-- so the infimum collapses to the singleton value.
/-- Owner-form companion of Lemma33.0.9 for the concave branch, stated directly with
`concaveConjugate`. -/
theorem concaveConjugate_negIndicator_singleton
    (x : X) (y : Y) :
    (-(δ[α](· | ({x} : Set X))))∗ y = ⟪x, y⟫ₚ := by
  rw [concaveConjugate_eq_iInf_pairing_sub]
  refine le_antisymm ?_ ?_
  · have hx :
        (⟪x, y⟫ₚ - (-(δ[α](· | ({x} : Set X))) : X → WithTopBot α) x : WithTopBot α) = ⟪x, y⟫ₚ := by
      change (⟪x, y⟫ₚ - -(δ[α](x | ({x} : Set X))) : WithTopBot α) = ⟪x, y⟫ₚ
      have hx0 : (δ[α](x | ({x} : Set X)) : WithTopBot α) = 0 := by
        exact indicator_of_mem ({x} : Set X) (by simp)
      rw [hx0, WithBotTop.sub_eq_add_neg, neg_neg, add_zero]
    rw [← hx]
    exact
      iInf_le
        (fun z : X ↦
          (⟪z, y⟫ₚ - (-(δ[α](· | ({x} : Set X))) : X → WithTopBot α) z : WithTopBot α))
        x
  · refine le_iInf ?_
    intro z
    by_cases hz : z = x
    · subst hz
      change (⟪z, y⟫ₚ : WithTopBot α) ≤ ⟪z, y⟫ₚ - -(δ[α](z | ({z} : Set X)))
      have hz0 : (δ[α](z | ({z} : Set X)) : WithTopBot α) = 0 := by
        exact indicator_of_mem ({z} : Set X) (by simp)
      rw [hz0, WithBotTop.sub_eq_add_neg, neg_neg, add_zero]
    · have hz' : z ∉ ({x} : Set X) := by
        simpa [Set.mem_singleton_iff] using hz
      change (⟪x, y⟫ₚ : WithTopBot α) ≤ ⟪z, y⟫ₚ - -(δ[α](z | ({x} : Set X)))
      have hzTop : (δ[α](z | ({x} : Set X)) : WithTopBot α) = ⊤ := by
        exact indicator_of_notMem ({x} : Set X) hz'
      rw [hzTop, WithBotTop.neg_top]
      have htop : ((⟪z, y⟫ₚ : WithTopBot α) - (⊥ : WithTopBot α)) = ⊤ := by
        exact WithBotTop.sub_bot (WithBotTop.coe_ne_bot (⟪z, y⟫ₚ : α))
      rw [htop]
      exact le_top

/-- The concave pairing of the negative indicator of the singleton `{x}` is the pairing with `x`,
in canonical pairing orientation. -/
theorem concavePairing_negIndicator_singleton
    (x : X) (y : Y) :
    ⟪y, (-(δ[α](· | ({x} : Set X))))⟫ᶜ = ⟪x, y⟫ₚ := by
  exact concaveConjugate_negIndicator_singleton x y

end NegIndicatorOfPoint

end Function
