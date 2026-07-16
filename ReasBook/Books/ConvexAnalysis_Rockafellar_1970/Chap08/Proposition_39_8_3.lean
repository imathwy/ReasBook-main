import ConvexAnalysis_Rockafellar_1970.Chap03.Text_13_1_3
import ConvexAnalysis_Rockafellar_1970.Chap03.Text_13_1_4
import ConvexAnalysis_Rockafellar_1970.Chap03.Text_13_0_2
import ConvexAnalysis_Rockafellar_1970.Chap08.Definition_39_8_1
import ConvexAnalysis_Rockafellar_1970.Chap08.Proposition_38_5_5

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped Pointwise Rockafellar

universe u v

namespace Set

/-!
Source/core/bridge triage for this item.

- `source-facing`: Proposition 39.8.3 records the homogeneity and additivity inequalities for the
  set inner product from Definition 39.8.1, together with the point specializations obtained when
  one side is a singleton.
- `core/canonical`: the owner abstraction is already the unconditional set pairing
  `Set.innerProduct`; `Set.HasInnerProduct` is only the companion maximin-minimax recognition
  predicate from Definition 39.8.1. The set operations are the canonical pointwise scalar action
  and Minkowski sum on sets, while the singleton clauses are already owned upstream by the support
  function `δᵛ(· | C)` and the sign-dual support-function bridge
  `x ↦ -δᵛ(-x | D)`.
- `bridge/view`: the two point clauses should therefore reuse those existing owner bridges rather
  than keep a parallel local singleton-pairing API.

Domain-style sampling used here:
- `Set.innerProduct` and `Set.HasInnerProduct` from `Definition_39_8_1`;
- `Function.innerProduct_neg_indicator_singleton_eq_convexPairing` from
  `Proposition_38_5_5`;
- `supportFunction_set_add_apply` from `Chap03.Text_13_1_3`;
- `neg_supportFunction_neg_eq_sInf_image_pairing_swap` from `Chap03.Text_13_0_2`.

Primitive data vs derived API:
- primitive owner data: `Set.innerProduct C D`;
- derived recognition data: `Set.HasInnerProduct C D`;
- derived API: the homogeneity/superadditivity inequalities, plus the singleton bridge views
  `C.innerProduct {y} = δᵛ[WithBotTop α](y | C)` and
  `({x} : Set E).innerProduct D = -δᵛ[WithBotTop α](-x | D)`,
  which make the point clauses immediate corollaries of the support-function owner theorems.
-/

section PositiveHomogeneity

variable {𝕜 : Type v} [Field 𝕜] [ConditionallyCompleteLinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
variable {E : Type u} [AddCommGroup E] [Module 𝕜 E] [HasLinearPairing E E 𝕜]

-- Proof sketch: unfold `Set.innerProduct` to the maximin formula from Definition 39.8.1 and
-- pull the positive scalar `λ` through the ambient inner product on the left variable. The
-- positivity assumption keeps the infimum/supremum order unchanged, so the owner-level scaling
-- identity holds directly for the unconditional set inner product.
/-- Proposition 39.8.3 (1): positive dilations of the left set scale the set inner product by the
same scalar. -/
theorem innerProduct_smul_left_of_pos
    (C D : Set E) {lam : 𝕜} (hlam : 0 < lam) :
    ((lam • C).innerProduct D : WithBotTop 𝕜) =
      (lam : WithBotTop 𝕜) * (C.innerProduct D : WithBotTop 𝕜) := sorry

-- Proof sketch: rewrite the right-set pairing through the maximin/minimax description of
-- `Set.innerProduct`, pull the positive scalar through the inner product in the right variable,
-- and use the same positivity argument to preserve the infimum order. This is again an
-- owner-level identity for the unconditional set inner product.
/-- Proposition 39.8.3 (2): positive dilations of the right set scale the set inner product by the
same scalar. -/
theorem innerProduct_smul_right_of_pos
    (C D : Set E) {lam : 𝕜} (hlam : 0 < lam) :
    (C.innerProduct (lam • D) : WithBotTop 𝕜) =
      (lam : WithBotTop 𝕜) * (C.innerProduct D : WithBotTop 𝕜) := sorry

end PositiveHomogeneity

section AdditivityInequalities

variable {𝕜 : Type v} [CommRing 𝕜] [ConditionallyCompleteLinearOrder 𝕜]
variable [IsOrderedAddMonoid 𝕜] [DenselyOrdered 𝕜]
variable {E : Type u} [AddCommMonoid E] [Module 𝕜 E] [HasLinearPairing E E 𝕜]

-- Proof sketch: expand the left-hand side as `sup_{x ∈ C + C'} inf_{y ∈ D} ⟪x, y⟫`, then use the
-- Minkowski-sum decomposition `x = x₁ + x₂` and additivity of the ambient inner product in the
-- left variable to compare with the separate suprema over `C` and `C'`. This superadditivity is
-- intrinsic to the unconditional owner `Set.innerProduct`.
/-- Proposition 39.8.3 (3): the set inner product is superadditive in the left set variable,
with no extra existence hypotheses. -/
theorem innerProduct_add_left_ge
    (C C' D : Set E) :
    ((C + C').innerProduct D : WithBotTop 𝕜) ≥
      (C.innerProduct D : WithBotTop 𝕜) + (C'.innerProduct D : WithBotTop 𝕜) := sorry

-- Proof sketch: rewrite the right-hand side through the minimax formula for `Set.innerProduct`
-- and compare `inf_{y ∈ D + D'} sup_{x ∈ C} ⟪x, y⟫` with the sum of the separate infima using
-- additivity of the ambient inner product in the right variable. This subadditivity also lives at
-- the unconditional owner level.
/-- Proposition 39.8.3 (4): the set inner product is subadditive in the right set variable,
with no extra existence hypotheses. -/
theorem innerProduct_add_right_le
    (C D D' : Set E) :
    (C.innerProduct (D + D') : WithBotTop 𝕜) ≤
      (C.innerProduct D : WithBotTop 𝕜) + (C.innerProduct D' : WithBotTop 𝕜) := sorry

end AdditivityInequalities

section SingletonRight

variable {α : Type v} [AddCommGroup α] [ConditionallyCompleteLinearOrder α]
variable {E : Type u} [HasPairing E E α] [HasPairingSwap E E α]

-- Proof sketch: Proposition 38.5.5 rewrites `C.innerProduct {y}` as the convex pairing of the
-- indicator of `C` with `y`, and Text 13.1.4 identifies that convex pairing with the support
-- value `δᵛ[WithBotTop ℝ](y | C)`.
/-- Owner bridge: pairing a set with the singleton right set `{y}` is exactly the support value of
`C` at `y`. -/
theorem innerProduct_singleton_right_eq_supportFunction
    (C : Set E) (y : E) :
    C.innerProduct ({y} : Set E) = δᵛ[WithBotTop α](y | C) := by
  rw [innerProduct]
  rw [Function.innerProduct_neg_indicator_singleton_eq_convexPairing]
  simpa using
    convexConjugate_indicatorFunction_eq_supportFunction_pointwise C y

end SingletonRight

section SingletonRightAdd

variable {𝕜 : Type v} [CommRing 𝕜] [ConditionallyCompleteLinearOrder 𝕜]
variable [IsOrderedAddMonoid 𝕜] [DenselyOrdered 𝕜]
variable {E : Type u} [AddCommMonoid E] [Module 𝕜 E]
variable [HasLinearPairing E E 𝕜] [HasPairingSwap E E 𝕜]

-- Proof sketch: rewrite each singleton-right pairing by
-- `innerProduct_singleton_right_eq_supportFunction`, then apply the owner theorem
-- `supportFunction_set_add_apply`.
/-- Proposition 39.8.3 (5): pairing a Minkowski sum on the left with a point `y`, viewed as the
singleton right set `{y}`, is additive in the left-set argument. -/
theorem innerProduct_add_singleton_right
    (C C' : Set E) (y : E) :
    ((C + C').innerProduct ({y} : Set E) : WithBotTop 𝕜) =
      (C.innerProduct ({y} : Set E) : WithBotTop 𝕜) +
        (C'.innerProduct ({y} : Set E) : WithBotTop 𝕜) := by
  rw [innerProduct_singleton_right_eq_supportFunction,
    innerProduct_singleton_right_eq_supportFunction,
    innerProduct_singleton_right_eq_supportFunction]
  simpa using supportFunction_set_add_apply C C' y

end SingletonRightAdd

section SingletonLeft

variable {𝕜 : Type v} [AddCommGroup 𝕜] [ConditionallyCompleteLinearOrder 𝕜]
variable [IsOrderedAddMonoid 𝕜]
variable {E : Type u} [AddCommGroup E]
variable [HasPairing E E 𝕜] [HasPairingSwap E E 𝕜] [HasPairingNegRight E E 𝕜]

local instance : Neg (WithBotTop 𝕜) := WithBotTop.instNeg

-- Proof sketch: collapse the outer supremum in `innerProduct_eq_iSup_iInf_pairing` against the
-- singleton `{x}`. The resulting infimum of the pairing values over `D` is exactly the sign-dual
-- support-function formula from `neg_supportFunction_neg_eq_sInf_image_pairing_swap`.
/-- Owner bridge: pairing the singleton left set `{x}` with `D` is the sign-dual support value
`-δᵛ[WithBotTop 𝕜](-x | D)`. -/
theorem innerProduct_singleton_left_eq_neg_supportFunction_neg
    (x : E) (D : Set E) :
    ({x} : Set E).innerProduct D = -δᵛ[WithBotTop 𝕜](-x | D) := by
  rw [innerProduct_eq_iSup_iInf_pairing]
  calc
    (⨆ z ∈ ({x} : Set E), ⨅ y ∈ D, (⟪z, y⟫ₚ : WithBotTop 𝕜))
        = (⨅ y ∈ D, (⟪x, y⟫ₚ : WithBotTop 𝕜)) := by
            simp
    _ = (⨅ y ∈ D, (⟪y, x⟫ₚ : WithBotTop 𝕜)) := by
          refine iInf_congr fun y ↦ ?_
          refine iInf_congr fun _ ↦ ?_
          exact
            congrArg ((↑) : 𝕜 → WithBotTop 𝕜) (HasPairingSwap.pairing_swap x y)
    _ = sInf ((fun y ↦ (⟪y, x⟫ₚ : WithBotTop 𝕜)) '' D) := by
          rw [sInf_image]
    _ = -δᵛ[WithBotTop 𝕜](-x | D) := by
          simpa using
            (neg_supportFunction_neg_eq_sInf_image_pairing_swap
              (C := D) (xStar := x)).symm

end SingletonLeft

section SingletonLeftAdd

variable {𝕜 : Type v} [CommRing 𝕜] [ConditionallyCompleteLinearOrder 𝕜]
variable [IsOrderedAddMonoid 𝕜] [DenselyOrdered 𝕜]
variable {E : Type u} [AddCommGroup E] [Module 𝕜 E]
variable [HasLinearPairing E E 𝕜] [HasPairingSwap E E 𝕜]

local instance : Neg (WithBotTop 𝕜) := WithBotTop.instNeg

-- Proof sketch: rewrite each singleton-left pairing by
-- `innerProduct_singleton_left_eq_neg_supportFunction_neg`, then apply `Neg.neg` to the owner
-- theorem `supportFunction_set_add_apply`.
/-- Proposition 39.8.3 (6): pairing a point `x`, viewed as the singleton left set `{x}`, with a
Minkowski sum on the right is additive in the right-set argument. -/
theorem innerProduct_singleton_left_add
    (x : E) (D D' : Set E) :
    (({x} : Set E).innerProduct (D + D') : WithBotTop 𝕜) =
      (({x} : Set E).innerProduct D : WithBotTop 𝕜) +
        (({x} : Set E).innerProduct D' : WithBotTop 𝕜) := sorry

end SingletonLeftAdd

end Set
