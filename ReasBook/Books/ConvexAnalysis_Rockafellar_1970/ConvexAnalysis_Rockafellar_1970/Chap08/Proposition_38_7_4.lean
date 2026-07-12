import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap08.Proposition_38_7_2
import ConvexAnalysis_Rockafellar_1970.Chap08.Theorem_38_3

noncomputable section

universe u v u' v'

namespace Bifunction

section

variable {𝕜 : Type*} {U : Type u} {X : Type v} {UStar : Type u'} {XStar : Type v'}
variable [Field 𝕜] [ConditionallyCompleteLinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
variable [AddCommGroup U] [Module 𝕜 U]
variable [AddCommMonoid X] [Module 𝕜 X]
variable [AddCommGroup UStar] [Module 𝕜 UStar]
variable [AddCommMonoid XStar] [Module 𝕜 XStar]
variable [HasLinearPairing U UStar 𝕜] [HasLinearPairing X XStar 𝕜]

open scoped Rockafellar

/-!
Source/core/bridge triage for this item.

- `source-facing`: Proposition 38.7.4 says that positive scalar rescaling preserves co-finiteness
  for Chapter 38 bifunctions.
- `core/canonical`: the relevant owners are the Chapter 38 rescaling owner `rightScalarMul`, the
  Chapter 38 adjoint-rescaling theorem `adjointFunction_rightScalarMul`, the positive-scalar
  convex-conjugacy owner `convexConjugate_rightScalarMul_eq_left_smul_of_pos`, and the
  bifunction-side co-finiteness owner `Bifunction.IsCofinite XStar UStar` from
  Proposition 38.7.2.
- `bridge/view`: this file adds no new owner; it is a direct preservation theorem for the
  canonical source-facing property.

Domain-style sampling used here:
- `rightScalarMul` from `Definition_38_2_2`;
- `convexConjugate_rightScalarMul_eq_left_smul_of_pos` from `Chap03.Theorem_16_1`,
  reused through the order-dual view `concaveConjugate`;
- `adjointFunction_rightScalarMul` from `Theorem_38_3`;
- `Bifunction.IsCofinite XStar UStar` from `Proposition_38_7_2`.

Primitive data vs derived API:
- primitive source-facing input: a bifunction `F : U → X → WithBotTop 𝕜` and a positive scalar
  `lam`;
- primitive owner hypothesis reused here: `IsCofinite XStar UStar F`;
- derived conclusion: `IsCofinite XStar UStar (rightScalarMul F lam)`.

Layer target: `source-facing`, proved as a thin owner-preservation theorem.
-/

-- Proof sketch: reuse the Chapter 38 owner theorem for the scaled lower pairing on the primal
-- slice, evaluate the adjoint-side pairing by changing to the underlying convex-conjugate owner
-- on the adjoint slice and applying the positive-scalar scaling theorem there, and then rewrite
-- the scaled adjoint by
-- `adjointFunction_rightScalarMul`.
/-- Proposition 38.7.4: a positive scalar multiple of a co-finite bifunction is again
co-finite. -/
theorem isCofinite_rightScalarMul
    {F : U → X → WithBotTop 𝕜} (hF : IsCofinite XStar UStar F)
    (lam : Set.Ioi (0 : 𝕜)) :
    IsCofinite XStar UStar (rightScalarMul F lam) := by
  sorry

end

end Bifunction
