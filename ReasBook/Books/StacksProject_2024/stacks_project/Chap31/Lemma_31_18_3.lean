import Mathlib
import StacksProject_2024.Chap31.Definition_31_18_2

-- Declarations for this item will be appended below by the statement pipeline.

namespace AlgebraicGeometry

open Scheme.IdealSheafData

-- Semantic recall: `lean_leansearch` only surfaced the ambient flatness owner `Flat`, while local
-- Chapter 31 precedent now records divisor sums through the canonical ideal-sheaf owner
-- `effectiveCartierDivisorSum`.

/-- Lemma 31.18.3: let `f : X ⟶ S` be a morphism of schemes. If `D₁, D₂ ⊆ X` are relative
effective Cartier divisors on `X/S`, then so is `D₁ + D₂`, formalized here by the ideal-sheaf
sum `effectiveCartierDivisorSum D₁ D₂`. -/
@[stacks 0B8U]
theorem isRelativeEffectiveCartierDivisor_sum
    {X S : Scheme} (f : X ⟶ S) (D₁ D₂ : X.IdealSheafData)
    [IsRelativeEffectiveCartierDivisor f D₁] [IsRelativeEffectiveCartierDivisor f D₂] :
    IsRelativeEffectiveCartierDivisor f (effectiveCartierDivisorSum D₁ D₂) := sorry

end AlgebraicGeometry
