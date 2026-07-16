import Mathlib
import StacksProject_2024.stacks_project.Chap31.Lemma_31_21_9

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open CategoryTheory
open CommRingCat
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry

section

variable (k : Type u) [Field k]

-- Semantic recall: `lean_leansearch` surfaced the quotient-spectrum closed-immersion owner
-- `AlgebraicGeometry.IsClosedImmersion.spec_of_quotient_mk`; local Chapter 31 precedent fixes
-- regular immersion near a point as `IsRegularImmersionNear`.

/-- The ideal `(x)` in `k[x]` used in the counterexample of Remark 31.21.10. -/
abbrev regularImmersionNearCounterexampleIdeal : Ideal (Polynomial k) :=
  Ideal.span ({Polynomial.X} : Set (Polynomial k))

/-- The affine line `X = A¹_k = Spec(k[x])` in Remark 31.21.10. -/
abbrev regularImmersionNearCounterexampleLine : Scheme.{u} :=
  Spec (of (Polynomial k))

/-- The first-order thickening `Y = Spec(k[x] / (x²))` in Remark 31.21.10, represented by the
canonical square `(x)^2`. -/
abbrev regularImmersionNearCounterexampleDoublePoint : Scheme.{u} :=
  Spec (of (Polynomial k ⧸ regularImmersionNearCounterexampleIdeal k ^ 2))

/-- The reduced closed point `Z = Spec(k[x] / (x))` in Remark 31.21.10. -/
abbrev regularImmersionNearCounterexampleClosedPoint : Scheme.{u} :=
  Spec (of (Polynomial k ⧸ regularImmersionNearCounterexampleIdeal k))

/-- The immersion `i : Z ⟶ Y` induced by the quotient map `k[x] / (x²) → k[x] / (x)`. -/
abbrev regularImmersionNearCounterexampleI :
    regularImmersionNearCounterexampleClosedPoint k ⟶
      regularImmersionNearCounterexampleDoublePoint k :=
  Spec.map
    (ofHom
      (Ideal.Quotient.factor
        (Ideal.pow_le_self two_ne_zero :
          regularImmersionNearCounterexampleIdeal k ^ 2 ≤
            regularImmersionNearCounterexampleIdeal k)))

/-- The immersion `j : Y ⟶ X` induced by the quotient map `k[x] → k[x] / (x²)`. -/
abbrev regularImmersionNearCounterexampleJ :
    regularImmersionNearCounterexampleDoublePoint k ⟶
      regularImmersionNearCounterexampleLine k :=
  Spec.map
    (ofHom
      (Ideal.Quotient.mk (regularImmersionNearCounterexampleIdeal k ^ 2)))

/-- Remark 31.21.10 (1): in the explicit dual-number thickening example, the composite
`j ∘ i` is a regular immersion near `z`. -/
@[stacks 0691]
theorem regularImmersionNear_comp_of_dualNumberThickening
    (z : regularImmersionNearCounterexampleClosedPoint k) :
    IsRegularImmersionNear
      (regularImmersionNearCounterexampleI k ≫ regularImmersionNearCounterexampleJ k) z := sorry

/-- Remark 31.21.10 (2): in the explicit dual-number thickening example, the target map `j`
is a regular immersion near the image of `z`. -/
@[stacks 0691]
theorem regularImmersionNear_target_of_dualNumberThickening
    (z : regularImmersionNearCounterexampleClosedPoint k) :
    IsRegularImmersionNear (regularImmersionNearCounterexampleJ k)
      ((regularImmersionNearCounterexampleI k).base z) := sorry

/-- Remark 31.21.10 (3): in the explicit dual-number thickening example, the pair `(i, j)`
does not satisfy `regularImmersionNearFactors` at `z`, so Lemma 31.21.9 part (1) fails here. -/
@[stacks 0691]
theorem not_regularImmersionNearFactors_of_dualNumberThickening
    (z : regularImmersionNearCounterexampleClosedPoint k) :
    ¬ regularImmersionNearFactors
      (regularImmersionNearCounterexampleI k) (regularImmersionNearCounterexampleJ k) z := sorry

end

end AlgebraicGeometry
