import Mathlib
import StacksProject_2024.Chap31.Lemma_31_13_7

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry

universe u

namespace AlgebraicGeometry

-- Semantic recall: `lean_leansearch` surfaced the canonical equality API
-- `Scheme.IdealSheafData.ext_iff`, and local Chapter 31 precedent uses
-- `IsEffectiveCartierDivisor` together with `effectiveCartierDivisorSum`
-- as the source-facing owners for effective Cartier divisors and their sum.
-- The source proof reduces to the affine algebra lemma `10.120.16`, but the
-- public surface here stays at the ideal-sheaf level on `X.IdealSheafData`.

variable {X : Scheme.{u}} (D Z Y : X.IdealSheafData)

/-- Lemma 31.13.9 (1): if the product ideal sheaf of the closed subschemes `Z`
and `Y` cuts out an effective Cartier divisor `D`, then `Z` is an effective
Cartier divisor. -/
theorem isEffectiveCartierDivisor_left_of_isEffectiveCartierDivisor_of_ideal_eq_mul
    (hD : D.ideal = fun U : X.affineOpens ↦ Z.ideal U * Y.ideal U)
    (hCartier : IsEffectiveCartierDivisor D) :
    IsEffectiveCartierDivisor Z := sorry

/-- Lemma 31.13.9 (2): if the product ideal sheaf of the closed subschemes `Z`
and `Y` cuts out an effective Cartier divisor `D`, then `Y` is an effective
Cartier divisor. -/
theorem isEffectiveCartierDivisor_right_of_isEffectiveCartierDivisor_of_ideal_eq_mul
    (hD : D.ideal = fun U : X.affineOpens ↦ Z.ideal U * Y.ideal U)
    (hCartier : IsEffectiveCartierDivisor D) :
    IsEffectiveCartierDivisor Y := sorry

/-- Lemma 31.13.9 (3): if the product ideal sheaf of the closed subschemes `Z`
and `Y` cuts out an effective Cartier divisor `D`, then `D` is the sum `Z + Y`.
In the current owner, this is the equality
`D = effectiveCartierDivisorSum Z Y`. -/
theorem eq_effectiveCartierDivisorSum_of_isEffectiveCartierDivisor_of_ideal_eq_mul
    (hD : D.ideal = fun U : X.affineOpens ↦ Z.ideal U * Y.ideal U)
    (hCartier : IsEffectiveCartierDivisor D) :
    D = effectiveCartierDivisorSum Z Y := sorry

end AlgebraicGeometry
