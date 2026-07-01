import ConvexAnalysis_Rockafellar_1970.Chap01.Defintion_4_8_1
import ConvexAnalysis_Rockafellar_1970.Chap07.Lemma33_0_9
import ConvexAnalysis_Rockafellar_1970.Chap08.Definition_38_5_2

noncomputable section

universe u v w

open scoped Rockafellar

namespace Function

section

variable {X : Type u} {Y : Type v} {α : Type w}
variable [AddGroup α] [ConditionallyCompleteLattice α]
variable [HasPairing X Y α]

local instance : HasPairing Y X α :=
  HasPairing.swap

/-!
Source/core/bridge triage:

- `source-facing`: Proposition 38.5.5 identifies the Chapter 38 inner product of `f` with the
  concave singleton indicator at `xStar`.
- `core/canonical`: the owner expressions are already `innerProduct` from Definition 38.5.2 and
  the Chapter 33 convex-pairing notation `⟪f, xStar⟫ᶠ = f⋆ xStar`.
- `bridge/view`: this item is therefore only a bridge between those existing owners. The actual
  singleton-indicator conjugate evaluation is already owned upstream by
  `concaveConjugate_negIndicator_singleton`, so this file should reuse that theorem
  directly rather than keeping a parallel local proof route.

Primary mathematical domain:
- Fenchel duality pairings for convex and concave conjugates.

Domain-style sampling used here:
- `innerProduct` and `innerProduct_eq_iSup_concaveConjugate_sub` from `Definition_38_5_2`;
- `convexConjugate_eq_iSup_pairing_sub` from the Chapter 12 owner API;
- `concaveConjugate_negIndicator_singleton` from `Lemma33_0_9`.
-/

-- Proof sketch: unfold `innerProduct` as `sup_x (g⋆ x - f x)` for
-- `g y = -δ[α](y | ({xStar} : Set Y))`. The concave conjugate of this negative singleton
-- indicator is the pairing function `x ↦ ⟪x, xStar⟫ₚ`, so the supremum becomes the Chapter 33
-- convex conjugate formula for `⟪f, xStar⟫ᶠ`.
/-- Proposition 38.5.5: the Section 38 inner product of `f` with the concave singleton indicator
`y ↦ -δ[α](y | ({xStar} : Set Y))` agrees with the Chapter 33 convex-pairing notation
`⟪f, xStar⟫ᶠ` for the conjugate value `f⋆ xStar`. -/
theorem innerProduct_neg_indicator_singleton_eq_convexPairing
    (f : X → WithBotTop α) (xStar : Y) :
    innerProduct f (-(δ[α](· | ({xStar} : Set Y)))) = ⟪f, xStar⟫ᶠ := by
  rw [innerProduct_eq_iSup_concaveConjugate_sub, convexConjugate_eq_iSup_pairing_sub]
  refine iSup_congr fun x ↦ ?_
  rw [concaveConjugate_negIndicator_singleton xStar x]

end

end Function
