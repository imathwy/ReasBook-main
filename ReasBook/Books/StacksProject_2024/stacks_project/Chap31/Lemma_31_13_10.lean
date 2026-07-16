import Mathlib
import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
import StacksProject_2024.stacks_project.Chap29.Definition_29_4_4
import StacksProject_2024.stacks_project.Chap31.Lemma_31_13_7

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry

universe u

namespace AlgebraicGeometry

-- Semantic recall: `lean_leansearch` surfaced the closed-subscheme union/intersection API, and
-- local Chapter 31 precedent fixes effective Cartier divisors on a scheme as `X.IdealSheafData`
-- with sum `effectiveCartierDivisorSum`. The source hypothesis that `D ∩ D'` is an effective
-- Cartier divisor on `D'` is therefore expressed by the pullback ideal sheaf `D.comap D'.subschemeι`.

/-- Lemma 31.13.10: if `D` and `D'` are effective Cartier divisors on a scheme `X` and the
scheme theoretic intersection `D ∩ D'`, viewed on `D'.subscheme` via `D.comap D'.subschemeι`, is
again an effective Cartier divisor on `D'.subscheme`, then the sum of divisors is cut out by the
intersection ideal sheaf. In the local `IdealSheafData` owner, this is the equality
`effectiveCartierDivisorSum D D' = D ⊓ D'`. -/
@[stacks 0C4R]
theorem effectiveCartierDivisorSum_eq_inf_of_isEffectiveCartierDivisor_comap_subschemeι
    {X : Scheme.{u}} (D D' : X.IdealSheafData)
    [IsEffectiveCartierDivisor D] [IsEffectiveCartierDivisor D']
    [IsEffectiveCartierDivisor (D.comap D'.subschemeι)] :
    effectiveCartierDivisorSum D D' = D ⊓ D' := sorry

/-- Source-form companion: under the same hypotheses, the sum `D + D'` is the scheme theoretic
union of the two effective Cartier divisors. -/
theorem subscheme_effectiveCartierDivisorSum_eq_schemeTheoreticUnion_of_isEffectiveCartierDivisor_comap_subschemeι
    {X : Scheme.{u}} (D D' : X.IdealSheafData)
    [IsEffectiveCartierDivisor D] [IsEffectiveCartierDivisor D']
    [IsEffectiveCartierDivisor (D.comap D'.subschemeι)] :
    (effectiveCartierDivisorSum D D').subscheme = Scheme.schemeTheoreticUnion D D' := sorry

end AlgebraicGeometry
