import Mathlib
import StacksProject_2024.stacks_project.Chap31.Definition_31_26_5

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry

end AlgebraicGeometry

namespace AlgebraicGeometry.Scheme

variable (X : Scheme.{u}) [IsLocallyNoetherian X] [IsIntegral X]
variable [PrimeDivisorDiscreteValuationRings X]

local notation "principalCoeff" => principalWeilDivisorCoeff X (primeDivisorDiscreteValuationRing X)

/-- The coefficient of the principal divisor attached to `f` is `\operatorname{ord}_Z(f)`. -/
theorem principalWeilDivisorCoeff_eq_primeDivisorOrder (f : X.functionFieldˣ) (Z : PrimeDivisor X) :
    principalCoeff f Z = X.primeDivisorOrder Z f := by
  simpa using
    (principalWeilDivisorCoeff_def X (primeDivisorDiscreteValuationRing X) f Z)

/-- The principal-divisor coefficient attached to `1` is `0`. -/
@[simp]
theorem principalWeilDivisorCoeff_one (Z : PrimeDivisor X) :
    principalCoeff 1 Z = 0 := by
  sorry

/-- Lemma 31.26.6: for `f, g ∈ R(X)ˣ`, the principal divisor of `f * g` is the sum of the
principal divisors of `f` and `g`, equivalently their coefficients add at each prime divisor. -/
@[simp]
theorem principalWeilDivisorCoeff_mul (f g : X.functionFieldˣ) (Z : PrimeDivisor X) :
    principalCoeff (f * g) Z = principalCoeff f Z + principalCoeff g Z := by
  sorry

/-- The negation of a principal divisor is principal, attached to the inverse function-field unit. -/
@[simp]
theorem principalWeilDivisorCoeff_inv (f : X.functionFieldˣ) (Z : PrimeDivisor X) :
    principalCoeff f⁻¹ Z = -principalCoeff f Z := by
  sorry

end AlgebraicGeometry.Scheme
