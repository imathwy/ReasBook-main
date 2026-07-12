import LinearRepresentations_Serre_1977.Chap01.Definition_1_1_4_1
import LinearRepresentations_Serre_1977.Chap02.Theorem_2_2_3_2
import LinearRepresentations_Serre_1977.Chap02.Remark_2_2_2_5
import LinearRepresentations_Serre_1977.FiniteToFintype

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped BigOperators Representation

universe u v u₁

namespace Representation

section

variable {G : Type u} [Group G] [Finite G]
variable {V : Type v} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
variable {ι : Type u₁} [Finite ι]
local instance : DecidableEq ι := Classical.decEq ι

-- Proof sketch: specialize `card_isomorphic_irreducible_summands_eq_character_pairing` to the
-- trivial representation `trivial ℂ G ℂ`. Its character is the constant function `1`, so the
-- character pairing reduces to the average `(Nat.card G : ℂ)⁻¹ * ∑ s : G, ρ.character s`.
/-- Exercise 2-2.3-6: if a finite-dimensional complex representation `ρ` is a direct sum of
irreducible subrepresentations `σ i`, then the number of summands isomorphic to the unit
representation is the normalized average of the character `ρ.character`, equivalently the pairing
`(χ|1)`. -/
theorem card_trivial_irreducible_summands_eq_character_average
    (ρ : Representation ℂ G V) (σ : ι → Subrepresentation ρ)
    (hinternal : DirectSum.IsInternal (fun i ↦ (σ i).toSubmodule))
    (hσ : ∀ i, (σ i).toRepresentation.IsIrreducible) :
    (Nat.card { i // Nonempty ((σ i).toRepresentation.Equiv (trivial ℂ G ℂ)) } : ℂ) =
      (Nat.card G : ℂ)⁻¹ * ∑ s : G, ρ.character s := by
  -- The trivial representation is irreducible because its carrier has complex dimension one.
  haveI : (trivial ℂ G ℂ).IsIrreducible := by
    simpa using
      isIrreducible_of_finrank_eq_one (trivial ℂ G ℂ)
        (by simp : Module.finrank ℂ ℂ = 1)
  -- The averaging formulas use the standard inverse of `|G|` in characteristic zero.
  have hcard_ne : (Nat.card G : ℂ) ≠ 0 := by
    exact_mod_cast Nat.card_pos.ne'
  letI : Invertible (Nat.card G : ℂ) := invertibleOfNonzero hcard_ne
  calc
    -- First identify the multiplicity of the trivial summand with the character pairing `(χ|1)`.
    (Nat.card { i // Nonempty ((σ i).toRepresentation.Equiv (trivial ℂ G ℂ)) } : ℂ) =
        ⟪ρ.character, (trivial ℂ G ℂ).character⟫ := by
          simpa using
            card_isomorphic_irreducible_summands_cast_eq_character_pairing
              ρ σ hinternal hσ (trivial ℂ G ℂ)
    -- Then expand the pairing against the trivial character, which is constantly equal to `1`.
    _ = (Nat.card G : ℂ)⁻¹ * ∑ s : G, ρ.character s := by
          rw [groupFunctionPairing_eq_card_inv_sum_apply_mul_inv_apply]
          simp [Representation.character, Representation.trivial]

end

end Representation
