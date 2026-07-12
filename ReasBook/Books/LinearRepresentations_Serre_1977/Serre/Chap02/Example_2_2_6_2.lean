import Mathlib
import LinearRepresentations_Serre_1977.Chap02.Exercise_2_2_6_3
import LinearRepresentations_Serre_1977.Chap02.Proposition_2_2_4_1
import LinearRepresentations_Serre_1977.FiniteToFintype

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators

universe u v

namespace Representation

noncomputable section

section

variable {G : Type u} [Group G] [Finite G]
variable {W : Type v} [AddCommGroup W] [Module ℂ W]


-- Proof sketch: apply the regular-character formula
-- `Representation.card_inv_mul_sum_char_mul_char_eq_finrank` to `σ ⟶ leftRegular`, then use
-- `leftRegular_character_eq_ite` to collapse the sum to the identity element.
/-- The intertwining space from `σ` into the regular representation has dimension `dim σ`. -/
theorem finrank_intertwiningMap_leftRegular
    (σ : Representation ℂ G W) [FiniteDimensional ℂ W] :
    Module.finrank ℂ (σ.IntertwiningMap (leftRegular ℂ G)) = Module.finrank ℂ W := by
  let ρ := leftRegular ℂ G
  have hsum :
      ∑ g : G, ρ.character g * σ.character g⁻¹ =
        (Nat.card G : ℂ) * Module.finrank ℂ W := by
    rw [Finset.sum_eq_single 1]
    · rw [leftRegular_character_one]
      simp [σ.char_one]
    · intro g _ hg
      rw [leftRegular_character_eq_zero_of_ne_one hg]
      simp
    · intro h
      exact False.elim (h (Finset.mem_univ 1))
  have h :
      (Module.finrank ℂ (σ.IntertwiningMap ρ) : ℂ) =
        Module.finrank ℂ W := by
    calc
      (Module.finrank ℂ (σ.IntertwiningMap ρ) : ℂ) =
          (Nat.card G : ℂ)⁻¹ *
            ∑ g : G, ρ.character g * σ.character g⁻¹ := by
              symm
              simpa using
                (card_inv_mul_sum_char_mul_char_eq_finrank σ ρ)
      _ = Module.finrank ℂ W := by
        rw [hsum]
        field_simp
  exact_mod_cast h

variable (σ : Representation ℂ G W) [σ.IsIrreducible]

-- Proof sketch: Exercise `2-2.6-3` already gives the canonical owner map from a family of
-- intertwining maps into the `σ`-isotypic component. A basis of the intertwining space therefore
-- yields the desired direct-sum evaluation equivalence; the basis is auxiliary data, so it stays
-- explicit in this bridge construction.
/-- A basis of `Hom_G(σ, ℂ[G])` indexed by `Fin (dim σ)` yields the corresponding equivariant
identification of the `σ`-isotypic summand of the regular representation with the direct sum of
`dim σ` copies of `σ`. This is a bridge/view built from the chosen basis, not an intrinsic owner
of the isotypic summand. -/
def leftRegular_isotypicComponent_equiv_directSum_of_basis
    (b : Module.Basis (Fin (Module.finrank ℂ W)) ℂ
      (σ.IntertwiningMap (leftRegular ℂ G))) :
    (directSum fun _ : Fin (Module.finrank ℂ W) ↦ σ).Equiv
      ((leftRegular ℂ G).isotypicSubrepresentation σ).toRepresentation :=
  letI : FiniteDimensional ℂ W := IsIrreducible.finiteDimensional_of_finite σ
  let ρ := leftRegular ℂ G
  (ρ.familyDirectSumEvaluation σ b).ofBijective
    (familyDirectSumEvaluation_bijective ρ σ b)

-- Proof sketch: first compute `dim Hom_G(σ, ℂ[G]) = dim σ`. Then choose a basis of that
-- intertwining space with index set `Fin (dim σ)` and apply the explicit-basis bridge above.
/-- Example 2-2.6-2: for an irreducible complex representation `σ` of a finite group, the
`σ`-isotypic summand of the regular representation is equivariantly equivalent to the direct sum
of `dim σ` copies of `σ`. -/
theorem leftRegular_isotypicComponent_nonempty_equiv_directSum :
    Nonempty
      ((directSum fun _ : Fin (Module.finrank ℂ W) ↦ σ).Equiv
        ((leftRegular ℂ G).isotypicSubrepresentation σ).toRepresentation) := by
  letI : FiniteDimensional ℂ W := IsIrreducible.finiteDimensional_of_finite σ
  let b : Module.Basis (Fin (Module.finrank ℂ W)) ℂ
      (σ.IntertwiningMap (leftRegular ℂ G)) :=
    Module.finBasisOfFinrankEq ℂ (σ.IntertwiningMap (leftRegular ℂ G))
      (finrank_intertwiningMap_leftRegular σ)
  exact ⟨leftRegular_isotypicComponent_equiv_directSum_of_basis σ b⟩

-- Proof sketch: apply the preceding direct-sum decomposition theorem and compare dimensions across
-- the resulting representation equivalence. The direct sum of `Module.finrank ℂ W` copies of `σ`
-- has dimension `Module.finrank ℂ W * Module.finrank ℂ W`.
/-- The complex dimension of the `σ`-isotypic summand of the regular representation is the square
of the degree of `σ`. -/
theorem finrank_leftRegular_isotypicComponent
    : Module.finrank ℂ (((leftRegular ℂ G).isotypicSubrepresentation σ).toSubmodule) =
      Module.finrank ℂ W ^ 2 := by
  letI : FiniteDimensional ℂ W := IsIrreducible.finiteDimensional_of_finite σ
  rcases leftRegular_isotypicComponent_nonempty_equiv_directSum σ with ⟨e⟩
  calc
    Module.finrank ℂ (((leftRegular ℂ G).isotypicSubrepresentation σ).toSubmodule) =
        Module.finrank ℂ
          (DirectSum (Fin (Module.finrank ℂ W)) (fun _ : Fin (Module.finrank ℂ W) ↦ W)) := by
            exact e.finrank_eq.symm
    _ = Module.finrank ℂ W ^ 2 := by
      simp [Module.finrank_directSum, pow_two]

end

end

end Representation
