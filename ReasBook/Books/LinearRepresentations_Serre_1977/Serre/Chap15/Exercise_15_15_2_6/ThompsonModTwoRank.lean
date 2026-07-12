import LinearRepresentations_Serre_1977.Chap15.Exercise_15_15_2_6.ThompsonDualHomothety

noncomputable section

open LinearMap (BilinForm)
open scoped Pointwise TensorProduct

universe u v w

open LinearMap.BilinForm

local notation:max p " •ℤ " E => (Representation.primeIdeal p • (⊤ : Submodule ℤ E))

section ThompsonExercise

variable {G : Type u} [Group G]
variable {E : Type v} [AddCommGroup E] [Module ℤ E]

section IntegralLatticeAmbient

variable [Module.Free ℤ E] [Module.Finite ℤ E]

-- Proof sketch: choose a characteristic vector for the self-dual form modulo `2`; invariance of
-- the form shows that its class in `E / 2E` is fixed by the action of `G`.
/-- Exercise 15-15.2-6 (5): a symmetric `G`-invariant form with self-dual integral lattice
admits a characteristic vector whose class modulo `2E` is fixed by `G`. -/
-- The proof solves the characteristic congruences over `ZMod 2` using the self-dual determinant
-- condition, then uses invariance of `B` to show the resulting class is fixed modulo `2E`.
theorem exists_characteristic_vector_mod_two_invariant
    (ρ : Representation ℤ G E) (B : BilinForm ℤ E) (hB_symm : B.IsSymm)
    (hB_invariant : B.IsInvariantUnder ρ) (hselfDual : B.IsSelfDualIntegralLattice) :
    ∃ x : E, B.IsCharacteristicModTwo x ∧
      ∀ g : G, ρ g x - x ∈ (2 •ℤ E) := by
  let n := Module.finrank ℤ E
  let b : Module.Basis (Fin n) ℤ E := Module.finBasis ℤ E
  let d : Fin n → ZMod 2 := fun i ↦ ((B (b i) (b i) : ℤ) : ZMod 2)
  have hdet : Matrix.det (B.toMatrix b) = 1 := hselfDual n b
  obtain ⟨x, hx_basis⟩ :=
    exists_vector_with_prescribed_pairings_mod_two_basis
      (E := E) b B hB_symm hdet d
  refine ⟨x, ?_, ?_⟩
  · -- Matching the diagonal basis values modulo `2` already gives a characteristic vector.
    apply isCharacteristicModTwo_of_basis_diagonal_congruence (E := E) b B hB_symm
    intro i
    rw [Int.modEq_iff_dvd]
    have hi : (((B (b i) (b i) : ℤ) : ZMod 2)) = ((B x (b i) : ℤ) : ZMod 2) := by
      simpa [d] using (hx_basis i).symm
    rw [ZMod.intCast_eq_intCast_iff_dvd_sub] at hi
    exact hi
  · intro g
    -- Invariance carries characteristic vectors to characteristic vectors, so their difference has
    -- even pairings with the chosen unimodular basis.
    have hx_char : B.IsCharacteristicModTwo x := by
      apply isCharacteristicModTwo_of_basis_diagonal_congruence (E := E) b B hB_symm
      intro i
      rw [Int.modEq_iff_dvd]
      have hi : (((B (b i) (b i) : ℤ) : ZMod 2)) = ((B x (b i) : ℤ) : ZMod 2) := by
        simpa [d] using (hx_basis i).symm
      rw [ZMod.intCast_eq_intCast_iff_dvd_sub] at hi
      exact hi
    have hxg_char : B.IsCharacteristicModTwo (ρ g x) :=
      isCharacteristicModTwo_map_of_invariant
        (ρ := ρ) (B := B) hB_invariant hx_char g
    have hpair_even :
        ∀ y : E, B (ρ g x - x) y ≡ 0 [ZMOD 2] :=
      sub_characteristic_vectors_pairing_even (B := B) hxg_char hx_char
    exact
      mem_two_mul_of_pairings_even_basis
        (E := E) b B hB_symm hdet (z := ρ g x - x) (fun i ↦ hpair_even (b i))

-- Proof sketch: by simplicity of the reduction modulo `2`, an invariant class in `E / 2E` must
-- vanish once the mod-`2` reduction is known to be nontrivial; applying this to a characteristic
-- vector with invariant mod-`2` class shows that the vector lies in `2E`, and substituting this
-- into the characteristic congruence gives that every diagonal value `B(y,y)` is even.
/-- Exercise 15-15.2-6 (6): if the reduction modulo `2` is irreducible and nontrivial, then any
characteristic vector whose class modulo `2E` is fixed by `G` lies in `2E`, and consequently the
form is even. -/
theorem characteristic_vector_mem_two_mul_and_form_even
    (ρ : Representation ℤ G E) (B : BilinForm ℤ E)
    (hρ₂ : ρ.HasIrreduciblePrimeReduction 2)
    (hρ₂_nontrivial : ρ.HasNontrivialPrimeReduction 2)
    (x : E) (hx : B.IsCharacteristicModTwo x)
    (hx_invariant : ∀ g : G, ρ g x - x ∈ (2 •ℤ E)) :
    x ∈ (2 •ℤ E) ∧ B.IsEven := by
  -- Route correction: keep the fixed-vector argument inside the canonical prime reduction, and
  -- only use the descended detector map to read back the zero class as `x ∈ 2E`.
  let ξ := prime_two_reduction_class (ρ := ρ) x
  have hξ_fixed :
      ∀ g : G,
        (ρ.primeStableLattice 2).reductionRepresentation g ξ = ξ := by
    intro g
    simpa [ξ] using
      prime_two_reduction_class_fixed_of_sub_mem_two_mul
        (ρ := ρ) (x := x) hx_invariant g
  -- Irreducibility and nontriviality force the fixed class to vanish.
  have hξ_zero : ξ = 0 := by
    exact
      fixed_class_eq_zero_of_irreducible_nontrivial_prime_reduction
        ρ hρ₂ hρ₂_nontrivial ξ hξ_fixed
  -- Translate that vanishing back to the integral statement `x ∈ 2E`.
  have hx_two : x ∈ (2 •ℤ E) := by
    simpa [ξ] using
      (prime_two_reduction_class_eq_zero_iff_mem_two_mul (ρ := ρ) x).1 hξ_zero
  -- Once the characteristic vector lies in `2E`, every diagonal value is even.
  exact ⟨hx_two, isEven_of_characteristicModTwo_of_mem_two_mul B x hx hx_two⟩

-- Proof sketch: combine the self-dual rescaling from part `(2)` with the automatic
-- nondegeneracy of positive definite forms, then apply parts `(4)`
-- and `(6)` to obtain an even positive definite unimodular integral quadratic form on `E`; the
-- additional mod-`2` nontriviality hypothesis excludes the one-dimensional trivial counterexample.
-- Finally apply the cited classification fact that such a lattice has rank divisible by `8`.
-- Exercise 15-15.2-6 (7): for a finite group action with simple prime reductions, the rank of
-- `E` is divisible by `8` provided the reduction modulo `2` is not the trivial representation.
/-- Helper for Exercise 15-15.2-6: the averaged positive definite invariant form from part `(a)`
is automatically nondegenerate, so Serre's part `(b)` can start from a nondegenerate owner. -/
theorem exists_positive_definite_invariant_nondegenerate_bilinForm
    [Finite G] (ρ : Representation ℤ G E) :
    ∃ B : BilinForm ℤ E, B.IsSymm ∧ B.IsInvariantUnder ρ ∧ B.toQuadraticMap.PosDef ∧
      B.Nondegenerate := by
  obtain ⟨B, hB_symm, hB_invariant, hB_pos⟩ :=
    exists_positive_definite_invariant_bilinForm (ρ := ρ)
  -- Positive definiteness upgrades the averaged form to a nondegenerate integral pairing.
  refine ⟨B, hB_symm, hB_invariant, hB_pos, ?_⟩
  exact nondegenerate_of_isSymm_of_posDef B hB_symm hB_pos

/-- Helper for Exercise 15-15.2-6: the completed prefix of part `(b)` supplies a positive
definite invariant form together with the current rational-homothety owner. -/
theorem exists_positive_definite_invariant_rational_dual_homothety
    [Finite G] (ρ : Representation ℤ G E) (hρ : ρ.HasSimplePrimeReductions) :
    ∃ B : BilinForm ℤ E, B.IsSymm ∧ B.IsInvariantUnder ρ ∧ B.toQuadraticMap.PosDef ∧
      LinearMap.BilinForm.DualIntegralLatticeIsRationalHomothety B := by
  obtain ⟨B, hB_symm, hB_invariant, hB_pos, hB_nondegenerate⟩ :=
    exists_positive_definite_invariant_nondegenerate_bilinForm (ρ := ρ)
  -- Route correction: package Serre's part `(a)` output together with the part `(b)` bridge
  -- before attempting the self-dual rescaling.
  let _ := hB_nondegenerate
  refine ⟨B, hB_symm, hB_invariant, hB_pos, ?_⟩
  exact
    rational_dual_lattice_eq_rational_homothety
      (ρ := ρ) (hρ := hρ) (B := B) hB_symm hB_invariant hB_pos

/-- Helper for Exercise 15-15.2-6: symmetry descends across a positive integral rescaling of an
integral bilinear form. -/
theorem LinearMap.BilinForm.isSymm_of_eq_nat_smul
    (B₀ B : BilinForm ℤ E) (m : ℕ) (hm : 0 < m)
    (hscale : B₀ = (m : ℤ) • B) (hB₀_symm : B₀.IsSymm) :
    B.IsSymm := by
  refine ⟨?_⟩
  intro x y
  have hm_ne : (m : ℤ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt hm
  have hxy : (m : ℤ) * B x y = (m : ℤ) * B y x := by
    -- Compare the two sides after rewriting them through the known symmetric rescaling `B₀`.
    calc
      (m : ℤ) * B x y = B₀ x y := by
            simp [hscale, LinearMap.smul_apply]
      _ = B₀ y x := hB₀_symm.eq x y
      _ = (m : ℤ) * B y x := by
            simp [hscale, LinearMap.smul_apply]
  exact mul_left_cancel₀ hm_ne hxy

/-- Helper for Exercise 15-15.2-6: `G`-invariance descends across a positive integral rescaling of
an integral bilinear form. -/
theorem LinearMap.BilinForm.isInvariantUnder_of_eq_nat_smul
    (ρ : Representation ℤ G E) (B₀ B : BilinForm ℤ E) (m : ℕ) (hm : 0 < m)
    (hscale : B₀ = (m : ℤ) • B) (hB₀_invariant : B₀.IsInvariantUnder ρ) :
    B.IsInvariantUnder ρ := by
  rw [LinearMap.BilinForm.isInvariantUnder_iff] at hB₀_invariant ⊢
  intro g x y
  have hm_ne : (m : ℤ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt hm
  have hxy : (m : ℤ) * B (ρ g x) (ρ g y) = (m : ℤ) * B x y := by
    -- Rewrite both sides through the scaled form `B₀`, then use the known invariance of `B₀`.
    calc
      (m : ℤ) * B (ρ g x) (ρ g y) = B₀ (ρ g x) (ρ g y) := by
            simp [hscale, LinearMap.smul_apply]
      _ = B₀ x y := hB₀_invariant g x y
      _ = (m : ℤ) * B x y := by
            simp [hscale, LinearMap.smul_apply]
  exact mul_left_cancel₀ hm_ne hxy

/-- Helper for Exercise 15-15.2-6: positivity descends across a positive integral rescaling of
an integral bilinear form. -/
theorem LinearMap.BilinForm.posDef_of_eq_nat_smul
    (B₀ B : BilinForm ℤ E) (m : ℕ) (hm : 0 < m)
    (hscale : B₀ = (m : ℤ) • B) (hpos : B₀.toQuadraticMap.PosDef) :
    B.toQuadraticMap.PosDef := by
  intro x hx
  have hscaled : 0 < ((m : ℤ) • B) x x := by
    -- Rewrite the positive-definite hypothesis on `B₀` through the displayed scaling equality.
    simpa [hscale, LinearMap.BilinMap.toQuadraticMap_apply] using hpos x hx
  have hmul : 0 < (m : ℤ) * B x x := by
    -- Evaluating the scaled form turns the equality into an integer product.
    simpa [LinearMap.smul_apply] using hscaled
  -- A positive multiple with positive coefficient forces the original diagonal value to be
  -- positive as well.
  simpa [LinearMap.BilinMap.toQuadraticMap_apply] using
    pos_of_mul_pos_right hmul (show 0 ≤ (m : ℤ) from (show 0 < (m : ℤ) from by exact_mod_cast hm).le)

-- Serre's part `(b)` is used in part `(d)` through a chosen positive definite invariant integral
-- form whose lattice is already self-dual.
/-- Helper for Exercise 15-15.2-6: once the part `(b)` homothety witness is expressed at the
integral-lattice owner level, one rescales the form to a self-dual integral form without changing
symmetry, invariance, or positive definiteness. -/
theorem exists_integral_rescale_selfDual_of_dual_homothety
    (ρ : Representation ℤ G E) (B₀ : BilinForm ℤ E)
    (hB₀_symm : B₀.IsSymm) (hB₀_invariant : B₀.IsInvariantUnder ρ)
    (hB₀_pos : B₀.toQuadraticMap.PosDef)
    (hdual : LinearMap.BilinForm.DualIntegralLatticeIsRationalHomothety B₀) :
    ∃ B : BilinForm ℤ E, B.IsSymm ∧ B.IsInvariantUnder ρ ∧ B.toQuadraticMap.PosDef ∧
      LinearMap.BilinForm.IsSelfDualIntegralLattice B := by
  rcases hdual with ⟨m, hm, B, hscale, hselfDual⟩
  refine ⟨B, ?_, ?_, ?_, hselfDual⟩
  · -- Use the dedicated rescaling lemma to recover symmetry from the scaled form `B₀`.
    exact LinearMap.BilinForm.isSymm_of_eq_nat_smul
      (B₀ := B₀) (B := B) (m := m) hm hscale hB₀_symm
  · -- Use the dedicated rescaling lemma to recover `G`-invariance from the scaled form `B₀`.
    exact LinearMap.BilinForm.isInvariantUnder_of_eq_nat_smul
      (ρ := ρ) (B₀ := B₀) (B := B) (m := m) hm hscale hB₀_invariant
  · -- Positivity descends across a positive integral rescaling.
    exact
      LinearMap.BilinForm.posDef_of_eq_nat_smul
        (B₀ := B₀) (B := B) (m := m) hm hscale hB₀_pos

/-- Helper for Exercise 15-15.2-6: Serre's part `(b)` is used in part `(d)` through a chosen
positive definite invariant integral form whose lattice is already self-dual. -/
theorem exists_positive_definite_invariant_selfDual_bilinForm
    [Finite G] (ρ : Representation ℤ G E) (hρ : ρ.HasSimplePrimeReductions) :
    ∃ B : BilinForm ℤ E, B.IsSymm ∧ B.IsInvariantUnder ρ ∧ B.toQuadraticMap.PosDef ∧
      LinearMap.BilinForm.IsSelfDualIntegralLattice B := by
  obtain ⟨B₀, hB₀_symm, hB₀_invariant, hB₀_pos, hdual⟩ :=
    exists_positive_definite_invariant_rational_dual_homothety (ρ := ρ) (hρ := hρ)
  -- Repackage the part `(a)` form through the rescaling output of part `(b)`.
  exact
    exists_integral_rescale_selfDual_of_dual_homothety
      (ρ := ρ) (B₀ := B₀) hB₀_symm hB₀_invariant hB₀_pos hdual

namespace LinearMap.BilinForm

/-- Source-cited external input for Exercise 15-15.2-6(d): every even positive definite
unimodular integral lattice has rank divisible by `8`.

Serre explicitly marks this as an external fact in part `(d)`. The local file therefore consumes it
as a hypothesis rather than proving the classification theorem or postulating it as an axiom. -/
class EvenUnimodularRankDivisibility (E : Type*) [AddCommGroup E] [Module ℤ E]
    [Module.Free ℤ E] [Module.Finite ℤ E] : Prop where
  rank_mod_eight :
    ∀ (B : BilinForm ℤ E), B.IsEven → B.toQuadraticMap.PosDef →
      B.IsSelfDualIntegralLattice → Module.finrank ℤ E ≡ 0 [MOD 8]

/-- Helper for Exercise 15-15.2-6: consume Serre's cited classification input saying that every
even positive definite unimodular integral lattice has rank divisible by `8`. -/
theorem finrank_mod_eight_of_isEven_of_posDef_of_isSelfDualIntegralLattice
    [EvenUnimodularRankDivisibility E]
    (B : BilinForm ℤ E) (h_even : B.IsEven) (h_pos : B.toQuadraticMap.PosDef)
    (hselfDual : B.IsSelfDualIntegralLattice) :
    Module.finrank ℤ E ≡ 0 [MOD 8] :=
  EvenUnimodularRankDivisibility.rank_mod_eight B h_even h_pos hselfDual

end LinearMap.BilinForm

theorem finrank_mod_eight_eq_zero_of_nontrivial_mod_two
    [LinearMap.BilinForm.EvenUnimodularRankDivisibility E]
    [Finite G]
    (ρ : Representation ℤ G E) (hρ : ρ.HasSimplePrimeReductions)
    (hρ₂_nontrivial : ρ.HasNontrivialPrimeReduction 2) :
    Module.finrank ℤ E ≡ 0 [MOD 8] := by
  obtain ⟨B, hB_symm, hB_invariant, hB_pos, hselfDual⟩ :=
    exists_positive_definite_invariant_selfDual_bilinForm (ρ := ρ) (hρ := hρ)
  obtain ⟨x, hx_char, hx_invariant⟩ :=
    exists_characteristic_vector_mod_two_invariant
      (ρ := ρ) (B := B) hB_symm hB_invariant hselfDual
  have hρ₂ : ρ.HasIrreduciblePrimeReduction 2 := hρ.irreducible 2
  obtain ⟨_, h_even⟩ :=
    characteristic_vector_mem_two_mul_and_form_even
      (ρ := ρ) (B := B) (hρ₂ := hρ₂) (hρ₂_nontrivial := hρ₂_nontrivial)
      x hx_char hx_invariant
  -- Package parts `(b)` through `(d)` into the cited even-unimodular rank-divisibility theorem.
  exact
    LinearMap.BilinForm.finrank_mod_eight_of_isEven_of_posDef_of_isSelfDualIntegralLattice
      (B := B) h_even hB_pos hselfDual

/-- Exercise 15-15.2-6(d): under Serre's source hypothesis `rank E ≥ 2`, the rank is divisible
by `8`. The rank hypothesis supplies the nontriviality of the mod-`2` reduction used in part
`(c)`. -/
theorem finrank_mod_eight_eq_zero
    [LinearMap.BilinForm.EvenUnimodularRankDivisibility E]
    [Finite G]
    (ρ : Representation ℤ G E) (hρ : ρ.HasSimplePrimeReductions)
    (hE_rank : 2 ≤ Module.finrank ℤ E) :
    Module.finrank ℤ E ≡ 0 [MOD 8] := by
  -- Serre assumes `n ≥ 2`; for a simple reduction this excludes the one-dimensional trivial
  -- mod-`2` representation, so the previously isolated part `(c)` conclusion applies.
  exact
    finrank_mod_eight_eq_zero_of_nontrivial_mod_two
      (ρ := ρ) (hρ := hρ)
      (hasNontrivialPrimeReduction_two_of_two_le_finrank (ρ := ρ) hρ hE_rank)

end IntegralLatticeAmbient

end ThompsonExercise
