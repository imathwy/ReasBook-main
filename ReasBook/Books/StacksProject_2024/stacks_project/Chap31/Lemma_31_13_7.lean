import StacksProject_2024.stacks_project.Chap31.Definition_31_13_1
import StacksProject_2024.stacks_project.Chap31.Definition_31_13_6

-- Declarations for this item will be appended below by the statement pipeline.

universe u

namespace AlgebraicGeometry

namespace Scheme.IdealSheafData

variable {X : Scheme.{u}}
variable [CategoryTheory.MonoidalCategory (RingedSpace.Modules X.toRingedSpace)]

/-- The product of two effective Cartier divisor ideal sheaves is again an effective Cartier
divisor. -/
theorem isEffectiveCartierDivisor_mul
    (D₁ D₂ : X.IdealSheafData)
    [D₁.IsEffectiveCartierDivisor] [D₂.IsEffectiveCartierDivisor] :
    (D₁ * D₂).IsEffectiveCartierDivisor := by
  sorry

/-- Lemma 31.13.7: the sum of two effective Cartier divisors is an effective Cartier divisor. -/
@[stacks 01WU]
theorem isEffectiveCartierDivisor_sum
    (D₁ D₂ : X.IdealSheafData)
    [D₁.IsEffectiveCartierDivisor] [D₂.IsEffectiveCartierDivisor] :
    (effectiveCartierDivisorSum D₁ D₂).IsEffectiveCartierDivisor := by
  simpa [effectiveCartierDivisorSum] using isEffectiveCartierDivisor_mul D₁ D₂

end Scheme.IdealSheafData

end AlgebraicGeometry
