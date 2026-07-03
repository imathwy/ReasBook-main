import Mathlib
import LinearRepresentations_Serre_1977.Chap02.Theorem_2_2_3_5
import LinearRepresentations_Serre_1977.Chap06.Proposition_6_6_3_1
import LinearRepresentations_Serre_1977.Chap06.Proposition_6_6_5_2

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators MonoidAlgebra Representation

noncomputable section

universe u v

namespace Representation

section

variable {k : Type*} [Field k] [IsAlgClosed k]
variable {G : Type u} [Group G] [Finite G]
variable {V : Type v} [AddCommGroup V] [Module k V]
variable (ρ : Representation k G V) [ρ.IsIrreducible]

local instance fintypeGCor6653 : Fintype G := Fintype.ofFinite G

-- Source/core/bridge triage:
-- * source-facing: `isIntegral_finrank_inv_sum_coeff_mul_character`.
-- * core/canonical owner: the central character `ω[ρ]`.
-- * upstream derived API: `IsIrreducible.finiteDimensional_of_finite ρ` supplies the
--   finite-dimensional structure required to evaluate `ω[ρ]` and `Module.finrank k V`.
-- * upstream derived API: the trace formula `centralCharacter_apply_eq_sum_character`, the
--   center-valued bridge `MonoidAlgebra.isIntegral_center_of_coeff_isIntegral`, and the canonical
--   transport theorem `map_isIntegral_int`.
-- Primitive data: the irreducible representation `ρ`, a central element
-- `u : Subalgebra.center k (k[G])`, and the coefficientwise integrality hypothesis `hu`.
-- Derived API: map that integrality along `ω[ρ]`, and then rewrite the result by the normalized
-- trace formula. Finite-dimensionality is derived internally from irreducibility because `G` is
-- finite.

/-- Corollary 6-6.5-3: if `ρ` is an irreducible representation of `G` over an algebraically
closed field `k`, and `u` is a central element of `k[G]` whose
coefficients are algebraic integers, then the
normalized sum of the coefficients of `u` weighted by the character of `ρ` is an algebraic
integer. For finite `G`, finite-dimensionality is automatic. -/
theorem isIntegral_finrank_inv_sum_coeff_mul_character
    (u : Subalgebra.center k (k[G])) (hu : ∀ s : G, IsIntegral ℤ ((u : k[G]) s)) :
    IsIntegral ℤ
      ((Module.finrank k V : k)⁻¹ *
        ∑ s : G, (u : k[G]) s * ρ.character s) := by
  letI : FiniteDimensional k V := IsIrreducible.finiteDimensional_of_finite ρ
  by_cases hfinrank : (Module.finrank k V : k) = 0
  -- When the rank vanishes in `k`, the normalized scalar is literally zero.
  · simpa [hfinrank] using (isIntegral_zero : IsIntegral ℤ (0 : k))
  -- Otherwise, transport integrality through `ω[ρ]` and rewrite its value by the trace formula.
  · simpa [centralCharacter_apply_eq_sum_character ρ u hfinrank] using
      map_isIntegral_int (ω[ρ])
        (MonoidAlgebra.isIntegral_center_of_coeff_isIntegral u hu)

end

end Representation
