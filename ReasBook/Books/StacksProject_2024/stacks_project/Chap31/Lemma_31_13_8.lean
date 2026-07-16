import Mathlib
import StacksProject_2024.stacks_project.Chap31.Definition_31_13_1
import StacksProject_2024.stacks_project.Chap31.Definition_31_13_6

-- Declarations for this item will be appended below by the statement pipeline.

universe u

namespace AlgebraicGeometry.Scheme.IdealSheafData

open CategoryTheory.MonoidalCategory

-- Semantic recall: the source-facing closed subscheme in this chapter is still
-- `D : X.IdealSheafData`, but the canonical effective-Cartier owner is the closed immersion
-- `D.subschemeι` from `Definition_31_13_1`; the divisor sum itself is the ideal-sheaf owner from
-- `Definition_31_13_6`.

variable {X : Scheme.{u}} (D D' : X.IdealSheafData)
variable [CategoryTheory.MonoidalCategory (RingedSpace.Modules X.toRingedSpace)]

/-- Lemma 31.13.8: if `D ⊆ D'` are effective Cartier divisors on `X`, encoded by the ideal-sheaf
inequality `D' ≤ D`, then there exists an effective Cartier divisor `D''` such that
`D' = D + D''`. The source-facing divisors remain ideal-sheaf data, while effectiveness is stated
through the canonical closed-immersion owner `D.subschemeι`. -/
@[stacks 02ON]
theorem exists_eq_effectiveCartierDivisorSum_of_le
    [D.IsEffectiveCartierDivisor] [D'.IsEffectiveCartierDivisor] (hle : D' ≤ D) :
    ∃ D'' : X.IdealSheafData,
      D''.IsEffectiveCartierDivisor ∧
        D' = effectiveCartierDivisorSum D D'' := sorry

/-- Companion ideal-sheaf form of Lemma 31.13.8: under `D' ≤ D`, there is an effective Cartier
divisor `D''` whose ideal sheaf is the product `D.ideal * D''.ideal`. -/
theorem exists_ideal_eq_mul_of_le
    [D.IsEffectiveCartierDivisor] [D'.IsEffectiveCartierDivisor] (hle : D' ≤ D) :
    ∃ D'' : X.IdealSheafData,
      D''.IsEffectiveCartierDivisor ∧
        D'.ideal = D.ideal * D''.ideal := by
  rcases exists_eq_effectiveCartierDivisorSum_of_le D D' hle with
    ⟨D'', hD'', hsum⟩
  refine ⟨D'', hD'', ?_⟩
  simpa [hsum] using ideal_effectiveCartierDivisorSum D D''

end AlgebraicGeometry.Scheme.IdealSheafData
