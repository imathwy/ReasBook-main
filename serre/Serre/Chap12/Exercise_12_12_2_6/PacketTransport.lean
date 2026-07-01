import Mathlib
import Serre.Chap02.Proposition_2_2_2_1
import Serre.Chap03.Theorem_3_3_2_1
import Serre.Chap06.Corollary_6_6_5_4
import Serre.Chap06.Proposition_6_6_5_5
import Serre.Chap12.Exercise_12_12_2_3.API
import Serre.Chap12.Exercise_12_12_2_6.CharacterBasisCoefficients
import Serre.Chap12.Exercise_12_12_2_6.FieldDenominatorPrelude
import Serre.Chap12.Exercise_12_12_2_6.ScalarExtensionPackets
import Serre.Chap12.Exercise_12_12_2_6.ScalarExtensionPairing
import Serre.Chap12.Proposition_12_12_2_1

noncomputable section

open scoped BigOperators
open scoped Representation

universe u v

namespace Representation

open CategoryTheory
open Exercise_12_12_2_6

namespace Exercise_12_12_2_6

section FieldPart

variable {G : Type u} [Group G] [Finite G]

local instance instFintypeGExercise_12_12_2_6_packet_transport : Fintype G := Fintype.ofFinite G

/-- Helper for Exercise 12-12.2-6: pairing a scaled visible packet against one constituent still
reads off exactly the corresponding quotient coefficient. -/
theorem scaled_packet_constituent_pairing_eq_coefficient_local
    {K1 : Type v} [Field K1] [CharZero K1]
    {ι : Type*} [Fintype ι]
    (χ : G → AlgebraicClosure K1)
    (ψ : ι → Rep.{max u v} (AlgebraicClosure K1) G)
    (e : ι → ℕ)
    (hψ_fd : ∀ j, FiniteDimensional (AlgebraicClosure K1) (ψ j))
    (hψ_pairwise : PairwiseNonisomorphic ψ)
    (hψ_irr : ∀ j, (ψ j).ρ.IsIrreducible)
    (hχ :
      χ = ∑ j, (e j : AlgebraicClosure K1) • (ψ j).ρ.character) :
    ∀ j, ⟪χ, (ψ j).ρ.character⟫ = (e j : AlgebraicClosure K1) := by
  intro j
  have hcard_ne : (Nat.card G : AlgebraicClosure K1) ≠ 0 := by
    exact Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  letI : Invertible (Nat.card G : AlgebraicClosure K1) := invertibleOfNonzero hcard_ne
  letI : FiniteDimensional (AlgebraicClosure K1) (ψ j) := hψ_fd j
  letI : (ψ j).ρ.IsIrreducible := hψ_irr j
  have hself_pair :
      ⟪(ψ j).ρ.character, (ψ j).ρ.character⟫ = (1 : AlgebraicClosure K1) := by
    -- Over an algebraically closed field, Schur's lemma makes the self-intertwining space
    -- one-dimensional.
    have hfinrank :
        Module.finrank (AlgebraicClosure K1)
            (Representation.IntertwiningMap (ψ j).ρ (ψ j).ρ) = 1 := by
      simpa using
        Representation.IsIrreducible.finrank_intertwiningMap_self (ρ := (ψ j).ρ)
    simpa [hfinrank] using
      (Representation.groupFunctionPairingOverField_character_eq_finrank_intertwiningMap
        (K := AlgebraicClosure K1) (G := G) (ρ := (ψ j).ρ) (σ := (ψ j).ρ))
  -- Expand the scaled packet on the left and collapse every off-diagonal summand by
  -- pairwise nonisomorphism.
  calc
    ⟪χ, (ψ j).ρ.character⟫
        = ⟪∑ l, (e l : AlgebraicClosure K1) • (ψ l).ρ.character,
            (ψ j).ρ.character⟫ := by
              rw [hχ]
    _ = ∑ l, (e l : AlgebraicClosure K1) * ⟪(ψ l).ρ.character, (ψ j).ρ.character⟫ := by
          simpa using
            groupFunctionPairing_sum_field_smul_left_universe_local
              (K' := K1) (G := G) (s := Finset.univ)
              (a := fun l ↦ (e l : AlgebraicClosure K1))
              (χ := fun l ↦ (ψ l).ρ.character) ((ψ j).ρ.character)
    _ = (e j : AlgebraicClosure K1) * ⟪(ψ j).ρ.character, (ψ j).ρ.character⟫ := by
          refine Finset.sum_eq_single j ?_ ?_
          · intro l _ hlj
            letI : FiniteDimensional (AlgebraicClosure K1) (ψ l) := hψ_fd l
            letI : (ψ l).ρ.IsIrreducible := hψ_irr l
            have hnot :
                ¬ Nonempty ((ψ l).ρ.Equiv (ψ j).ρ) := by
              intro hIso
              apply hψ_pairwise hlj
              rcases hIso with ⟨eIso⟩
              simpa using (show Nonempty (ψ l ≅ ψ j) from ⟨Rep.mkIso eIso⟩)
            have hpair_zero :
                ⟪(ψ l).ρ.character, (ψ j).ρ.character⟫ = (0 : AlgebraicClosure K1) := by
              exact
                Representation.groupFunctionPairingOverField_character_eq_zero_of_not_isomorphic
                  (K := AlgebraicClosure K1) (G := G) (ρ := (ψ l).ρ) (σ := (ψ j).ρ) hnot
            rw [hpair_zero, mul_zero]
          · intro hj
            exact (hj (Finset.mem_univ j)).elim
    _ = (e j : AlgebraicClosure K1) := by
          simp [hself_pair]

/-- Helper for Exercise 12-12.2-6: once a packet permutation transports constituent characters,
the scaled visible packet forces the quotient coefficients to be constant along that permutation. -/
theorem scaled_packet_coeff_transport_invariant_local
    {K1 : Type v} [Field K1] [CharZero K1]
    (ρ : Rep K1 G)
    (n : ℕ+)
    {ι : Type*} [Fintype ι]
    (ψ : ι → Rep.{max u v} (AlgebraicClosure K1) G)
    (e : ι → ℕ)
    (hψ_fd : ∀ i, FiniteDimensional (AlgebraicClosure K1) (ψ i))
    (hψ_pairwise : PairwiseNonisomorphic ψ)
    (hψ_irr : ∀ i, (ψ i).ρ.IsIrreducible)
    (hscaled_packet :
      ((IsScalarTower.toAlgHom ℤ K1 (AlgebraicClosure K1)).compLeft G)
          ((((n : ℕ) : K1)⁻¹) • ρ.ρ.character) =
        ∑ i, (e i : AlgebraicClosure K1) • (ψ i).ρ.character)
    (σ : (AlgebraicClosure K1) ≃ₐ[K1] (AlgebraicClosure K1))
    (τ : Equiv.Perm ι)
    (hchar : ∀ i : ι, ∀ g : G, σ ((ψ i).ρ.character g) = (ψ (τ i)).ρ.character g) :
    ∀ i, e (τ i) = e i := by
  intro i
  have htransport_packet :
      ((IsScalarTower.toAlgHom ℤ K1 (AlgebraicClosure K1)).compLeft G)
          ((((n : ℕ) : K1)⁻¹) • ρ.ρ.character) =
        ∑ j, (e (τ⁻¹ j) : AlgebraicClosure K1) • (ψ j).ρ.character := by
    -- Apply the field automorphism to the scaled packet identity and then reindex along `τ`.
    ext g
    have hfixed :
        σ
            (((IsScalarTower.toAlgHom ℤ K1 (AlgebraicClosure K1)).compLeft G)
                ((((n : ℕ) : K1)⁻¹) • ρ.ρ.character) g) =
          ((IsScalarTower.toAlgHom ℤ K1 (AlgebraicClosure K1)).compLeft G)
            ((((n : ℕ) : K1)⁻¹) • ρ.ρ.character) g := by
      simp [smul_eq_mul, map_mul]
    calc
      ((IsScalarTower.toAlgHom ℤ K1 (AlgebraicClosure K1)).compLeft G)
          ((((n : ℕ) : K1)⁻¹) • ρ.ρ.character) g
          =
            σ
              (((IsScalarTower.toAlgHom ℤ K1 (AlgebraicClosure K1)).compLeft G)
                  ((((n : ℕ) : K1)⁻¹) • ρ.ρ.character) g) := by
                    exact hfixed.symm
      _ = σ ((∑ j, (e j : AlgebraicClosure K1) • (ψ j).ρ.character) g) := by
            rw [hscaled_packet]
      _ = ∑ j, (e j : AlgebraicClosure K1) * (ψ (τ j)).ρ.character g := by
            simp [smul_eq_mul, map_mul, hchar]
      _ = ∑ j, (e (τ⁻¹ j) : AlgebraicClosure K1) * (ψ j).ρ.character g := by
            exact
              Fintype.sum_equiv τ
                (fun j : ι ↦ (e j : AlgebraicClosure K1) * (ψ (τ j)).ρ.character g)
                (fun j : ι ↦
                  (e (τ⁻¹ j) : AlgebraicClosure K1) * (ψ j).ρ.character g)
                (by
                  intro j
                  simp)
      _ = (∑ j, (e (τ⁻¹ j) : AlgebraicClosure K1) • (ψ j).ρ.character) g := by
            simp [smul_eq_mul]
  have horig :
      ⟪((IsScalarTower.toAlgHom ℤ K1 (AlgebraicClosure K1)).compLeft G)
          ((((n : ℕ) : K1)⁻¹) • ρ.ρ.character),
        (ψ (τ i)).ρ.character⟫ =
        (e (τ i) : AlgebraicClosure K1) := by
    exact
      scaled_packet_constituent_pairing_eq_coefficient_local
        (G := G)
        (((IsScalarTower.toAlgHom ℤ K1 (AlgebraicClosure K1)).compLeft G)
          ((((n : ℕ) : K1)⁻¹) • ρ.ρ.character))
        ψ e hψ_fd hψ_pairwise hψ_irr hscaled_packet (τ i)
  have htransport :
      ⟪((IsScalarTower.toAlgHom ℤ K1 (AlgebraicClosure K1)).compLeft G)
          ((((n : ℕ) : K1)⁻¹) • ρ.ρ.character),
        (ψ (τ i)).ρ.character⟫ =
        (e i : AlgebraicClosure K1) := by
    simpa using
      scaled_packet_constituent_pairing_eq_coefficient_local
        (G := G)
        (((IsScalarTower.toAlgHom ℤ K1 (AlgebraicClosure K1)).compLeft G)
          ((((n : ℕ) : K1)⁻¹) • ρ.ρ.character))
        ψ (fun j ↦ e (τ⁻¹ j)) hψ_fd hψ_pairwise hψ_irr htransport_packet (τ i)
  -- Compare the original coefficient with the transported coefficient on the same constituent.
  exact Nat.cast_injective (horig.symm.trans htransport)

/-- Helper for Exercise 12-12.2-6: transporting an algebraic-closure character through a
base-field automorphism keeps it inside the algebraic-closure character ring. -/
theorem transported_constituent_character_mem_characterRing_local
    {K1 : Type v} [Field K1] [CharZero K1]
    (ψ0 : Rep.{max u v} (AlgebraicClosure K1) G)
    [FiniteDimensional (AlgebraicClosure K1) ψ0]
    (σ : (AlgebraicClosure K1) ≃ₐ[K1] (AlgebraicClosure K1)) :
    (fun g ↦ σ (ψ0.ρ.character g)) ∈ R[AlgebraicClosure K1](G) := by
  -- A field automorphism only changes coefficients, so it transports honest characters to honest
  -- characters over the same algebraically closed field.
  simpa using
    map_mem_characterRingOverField_local
      (G := G) (f := (σ.restrictScalars ℤ).toAlgHom) (χ := ψ0.ρ.character)
      (rep_character_mem_characterRingOverField_universe_local
        (K' := AlgebraicClosure K1) (H := G) (ρ := ψ0.ρ))

/-- Helper for Exercise 12-12.2-6: applying a base-field automorphism to Serre's normalized
pairing is the same as transporting both arguments coefficientwise. -/
theorem algEquiv_groupFunctionPairing_apply_local
    {K1 : Type v} [Field K1] [CharZero K1]
    (σ : (AlgebraicClosure K1) ≃ₐ[K1] (AlgebraicClosure K1))
    (χ ψ : G → AlgebraicClosure K1) :
    σ ⟪χ, ψ⟫ = ⟪(fun g ↦ σ (χ g)), fun g ↦ σ (ψ g)⟫ := by
  -- Push the automorphism through the normalized finite sum defining the pairing.
  simp [Representation.groupFunctionPairingOverField, map_mul, map_sum]

/-- Helper for Exercise 12-12.2-6: transporting the character of an irreducible constituent
through a base-field automorphism preserves the self-pairing value `1`. -/
theorem transported_irreducible_character_self_pairing_eq_one_local
    {K1 : Type v} [Field K1] [CharZero K1]
    (ψ0 : Rep.{max u v} (AlgebraicClosure K1) G)
    [FiniteDimensional (AlgebraicClosure K1) ψ0]
    [ψ0.ρ.IsIrreducible]
    (σ : (AlgebraicClosure K1) ≃ₐ[K1] (AlgebraicClosure K1)) :
    ⟪(fun g ↦ σ (ψ0.ρ.character g)), fun g ↦ σ (ψ0.ρ.character g)⟫ =
      (1 : AlgebraicClosure K1) := by
  have hcard_ne : (Nat.card G : AlgebraicClosure K1) ≠ 0 := by
    exact Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  letI : Invertible (Nat.card G : AlgebraicClosure K1) := invertibleOfNonzero hcard_ne
  have hself :
      ⟪ψ0.ρ.character, ψ0.ρ.character⟫ = (1 : AlgebraicClosure K1) := by
    have hfinrank :
        Module.finrank (AlgebraicClosure K1)
            (Representation.IntertwiningMap ψ0.ρ ψ0.ρ) = 1 := by
      -- Schur's lemma identifies the self-intertwining space of an irreducible constituent.
      simpa using Representation.IsIrreducible.finrank_intertwiningMap_self (ρ := ψ0.ρ)
    -- The normalized self-pairing is the dimension of the self-intertwining space.
    simpa [hfinrank] using
      (Representation.groupFunctionPairingOverField_character_eq_finrank_intertwiningMap
        (K := AlgebraicClosure K1) (G := G) (ρ := ψ0.ρ) (σ := ψ0.ρ))
  -- Apply the automorphism to the usual irreducible self-pairing formula and then simplify.
  calc
    ⟪(fun g ↦ σ (ψ0.ρ.character g)), fun g ↦ σ (ψ0.ρ.character g)⟫
        = σ ⟪ψ0.ρ.character, ψ0.ρ.character⟫ := by
            symm
            exact
              algEquiv_groupFunctionPairing_apply_local
                (G := G) (σ := σ) ψ0.ρ.character ψ0.ρ.character
    _ = σ (1 : AlgebraicClosure K1) := by
          rw [hself]
    _ = 1 := by simp

/-- Helper for Exercise 12-12.2-6: a finite-dimensional irreducible representation has positive
degree. -/
private theorem irreducible_rep_finrank_pos_local
    {K1 : Type v} [Field K1]
    (V : Rep.{max u v} K1 G)
    [FiniteDimensional K1 V]
    [V.ρ.IsIrreducible] :
    0 < Module.finrank K1 V := by
  have hV_nontriv : Nontrivial V := by
    -- An irreducible representation cannot live on the zero module, or else `⊥ = ⊤`.
    by_contra hV_trivial
    letI : Subsingleton V := not_nontrivial_iff_subsingleton.mp hV_trivial
    have hbot : (⊥ : Subrepresentation V.ρ) = ⊤ := by
      apply Subrepresentation.toSubmodule_injective
      ext x
      constructor
      · intro _
        trivial
      · intro _
        simpa using (Subsingleton.elim x 0)
    exact bot_ne_top hbot
  letI : Nontrivial V := hV_nontriv
  exact Module.finrank_pos

/-- Helper for Exercise 12-12.2-6: if the visible packet multiplicity `d i` is positive and
splits as `n * e i`, then the quotient coefficient `e i` is already positive. -/
theorem visible_packet_quotient_coeff_pos_local
    (n : ℕ+)
    {ι : Type*}
    (d e : ι → ℕ)
    (hd_pos : ∀ i, 0 < d i)
    (he : ∀ i, d i = (n : ℕ) * e i) :
    ∀ i, 0 < e i := by
  intro i
  by_contra hei_nonpos
  have hei_zero : e i = 0 := Nat.eq_zero_of_not_pos hei_nonpos
  have hdi_zero : d i = 0 := by
    rw [he i, hei_zero, Nat.mul_zero]
  exact (Nat.lt_irrefl 0) (hdi_zero ▸ hd_pos i)

/-- Helper for Exercise 12-12.2-6: an integral square sum equal to `1` has exactly one nonzero
coefficient, and that coefficient is `1` or `-1`. -/
theorem integer_coefficients_eq_singleton_of_sq_sum_eq_one_local
    {ι : Type*} [Fintype ι]
    (c : ι → ℤ)
    (h : ∑ i, (c i) ^ 2 = 1) :
    ∃ i, (c i = 1 ∨ c i = -1) ∧ ∀ j, j ≠ i → c j = 0 := by
  classical
  have hnotallzero : ¬ ∀ i, c i = 0 := by
    intro hzero
    have hsum_zero : ∑ i, (c i)^2 = 0 := by
      simp [hzero]
    linarith
  obtain ⟨i, hi_nonzero⟩ : ∃ i, c i ≠ 0 := by
    simpa [not_forall] using hnotallzero
  have hi_sq_le : (c i)^2 ≤ 1 := by
    calc
      (c i)^2 ≤ ∑ j, (c j)^2 := by
        simpa using
          (Finset.single_le_sum (fun j _ ↦ sq_nonneg (c j)) (Finset.mem_univ i) :
            (c i)^2 ≤ ∑ j, (c j)^2)
      _ = 1 := h
  have hi_sq_eq : (c i)^2 = 1 := by
    exact Int.sq_eq_one_of_sq_le_three (le_trans hi_sq_le (by norm_num)) hi_nonzero
  have hi_sign : c i = 1 ∨ c i = -1 := by
    exact sq_eq_one_iff.mp hi_sq_eq
  refine ⟨i, hi_sign, ?_⟩
  intro j hji
  have hsum_erase :
      Finset.sum (Finset.univ.erase i) (fun k ↦ (c k)^2) + (c i)^2 = 1 := by
    calc
      Finset.sum (Finset.univ.erase i) (fun k ↦ (c k)^2) + (c i)^2 = ∑ k, (c k)^2 := by
        simpa using (Finset.sum_erase_add (s := Finset.univ) (f := fun k ↦ (c k)^2)
          (Finset.mem_univ i))
      _ = 1 := h
  have herase_zero : Finset.sum (Finset.univ.erase i) (fun k ↦ (c k)^2) = 0 := by
    linarith
  have hj_sq_le :
      (c j)^2 ≤ Finset.sum (Finset.univ.erase i) (fun k ↦ (c k)^2) := by
    have hj_mem : j ∈ Finset.univ.erase i := by
      simp [hji]
    simpa using
      (Finset.single_le_sum (fun k _ ↦ sq_nonneg (c k)) hj_mem :
        (c j)^2 ≤ Finset.sum (Finset.univ.erase i) (fun k ↦ (c k)^2))
  have hj_sq_eq_zero : (c j)^2 = 0 := by
    have hj_sq_nonneg : 0 ≤ (c j)^2 := sq_nonneg (c j)
    linarith
  exact sq_eq_zero_iff.mp hj_sq_eq_zero

/-- Helper for Exercise 12-12.2-6: over the algebraic closure, a character-ring element with
irreducible self-pairing and positive value at `1` should come from an honest irreducible
representation. -/
theorem exists_irreducible_rep_character_eq_of_mem_characterRing_self_pairing_eq_one_local
    {K1 : Type v} [Field K1] [CharZero K1]
    (χ : G → AlgebraicClosure K1)
    (hχ : χ ∈ R[AlgebraicClosure K1](G))
    (hpair : ⟪χ, χ⟫ = (1 : AlgebraicClosure K1))
    (n : ℕ)
    (hn_pos : 0 < n)
    (hχ_one : χ 1 = (n : AlgebraicClosure K1)) :
    ∃ τ : Rep.{max u v} (AlgebraicClosure K1) G,
      FiniteDimensional (AlgebraicClosure K1) τ ∧ τ.ρ.IsIrreducible ∧ τ.ρ.character = χ := by
  classical
  let H := Shrink.{v} G
  let e : H ≃* G := Shrink.mulEquiv
  let χH : H → AlgebraicClosure K1 := fun h ↦ χ (e h)
  have hχH : χH ∈ R[AlgebraicClosure K1](H) := by
    -- Move the character-ring element to the same-universe owner needed for the irreducible
    -- basis argument.
    simpa [H, e, χH] using
      (mem_characterRingOverField_precomp_mulEquiv_local
        (K' := AlgebraicClosure K1) (G₀ := G) (H := H) (e := e) (hχ := hχ))
  have hpairH : ⟪χH, χH⟫ = (1 : AlgebraicClosure K1) := by
    -- The normalized pairing is invariant under precomposition by a multiplicative equivalence.
    exact
      (groupFunctionPairingOverField_precomp_mulEquiv_local
        (G := G) (H := H) (e := e) (φ := χ) (ψ := χ)).trans hpair
  have hχH_one : χH 1 = (n : AlgebraicClosure K1) := by
    simpa [H, e, χH] using hχ_one
  have hcard_ne : (Nat.card H : AlgebraicClosure K1) ≠ 0 := by
    exact Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  letI : Invertible (Nat.card H : AlgebraicClosure K1) := invertibleOfNonzero hcard_ne
  obtain ⟨ι, _, π, hπ_pairwise, hπ_complete⟩ :=
    exists_complete_pairwise_nonisomorphic_simple_family_local
      (K := AlgebraicClosure K1) (G := H)
  letI : Fintype ι := inferInstance
  let x : R[AlgebraicClosure K1](H) := ⟨χH, hχH⟩
  let b :=
    irreducible_characters_basis_of_complete_family
      (AlgebraicClosure K1) π hπ_pairwise hπ_complete
  let c : ι → ℤ := b.repr x
  have hx :
      ∑ i, c i • (π i).character = χH := by
    -- Expand `χ` in the irreducible-character basis over the algebraic closure.
    simpa [b, c, irreducible_characters_basis_of_complete_family_apply,
      FDRep.irreducibleCharacter_apply] using
      congrArg (fun z : R[AlgebraicClosure K1](H) ↦ (z : H → AlgebraicClosure K1))
        (b.sum_repr x)
  have hself_pair :
      ∀ i, ⟪(π i).character, (π i).character⟫ = (1 : AlgebraicClosure K1) := by
    intro i
    letI : Simple (π i) := hπ_complete.isSimple i
    letI : Representation.IsIrreducible (π i).ρ := FDRep.isIrreducible_of_simple (π i)
    have hfinrank :
        Module.finrank (AlgebraicClosure K1)
            (Representation.IntertwiningMap (π i).ρ (π i).ρ) = 1 := by
      -- Schur's lemma identifies the self-intertwining space with the scalars.
      simpa using Representation.IsIrreducible.finrank_intertwiningMap_self (ρ := (π i).ρ)
    simpa [hfinrank] using
      (Representation.groupFunctionPairingOverField_character_eq_finrank_intertwiningMap
        (K := AlgebraicClosure K1) (G := H) (ρ := (π i).ρ) (σ := (π i).ρ))
  have hcoeff_pair :
      ∀ i, ⟪χH, (π i).character⟫ = (c i : AlgebraicClosure K1) := by
    intro i
    calc
      ⟪χH, (π i).character⟫
          = (((c i : ℤ) : AlgebraicClosure K1) *
              ⟪(π i).character, (π i).character⟫) := by
                simpa [x, b, c] using
                  basis_coefficient_pairing_eq_local
                    (K := AlgebraicClosure K1) (G := H)
                    (π := π) hπ_pairwise hπ_complete x i
      _ = (c i : AlgebraicClosure K1) := by
            simp [hself_pair i]
  have hpair_expand :
      ⟪χH, χH⟫ = ((∑ i, (c i)^2 : ℤ) : AlgebraicClosure K1) := by
    calc
      ⟪χH, χH⟫ = ⟪∑ i, c i • (π i).character, χH⟫ := by
        rw [hx]
      _ =
          ∑ i, (((c i : ℤ) : AlgebraicClosure K1) * ⟪(π i).character, χH⟫) := by
            simpa using
              groupFunctionPairing_sum_zsmul_left_overField_local
                (K := AlgebraicClosure K1) (G := H)
                (s := Finset.univ) (a := c) (χ := fun i ↦ (π i).character) (ψ := χH)
      _ =
          ∑ i, (((c i : ℤ) : AlgebraicClosure K1) * ⟪χH, (π i).character⟫) := by
            refine Finset.sum_congr rfl ?_
            intro i _
            rw [Representation.groupFunctionPairing_comm]
      _ = ∑ i, (((c i)^2 : ℤ) : AlgebraicClosure K1) := by
            refine Finset.sum_congr rfl ?_
            intro i _
            rw [hcoeff_pair i]
            simp [pow_two]
      _ = ((∑ i, (c i)^2 : ℤ) : AlgebraicClosure K1) := by
            simp
  have hsq_eq_one : ∑ i, (c i)^2 = 1 := by
    have hcast_sq_eq_one :
        (((∑ i, (c i)^2 : ℤ) : AlgebraicClosure K1)) = ((1 : ℤ) : AlgebraicClosure K1) := by
      calc
        (((∑ i, (c i)^2 : ℤ) : AlgebraicClosure K1)) = ⟪χH, χH⟫ := by
          symm
          exact hpair_expand
        _ = (1 : AlgebraicClosure K1) := hpairH
        _ = ((1 : ℤ) : AlgebraicClosure K1) := by norm_num
    exact_mod_cast hcast_sq_eq_one
  obtain ⟨i, hi_sign, hzero⟩ :=
    integer_coefficients_eq_singleton_of_sq_sum_eq_one_local (c := c) hsq_eq_one
  have hdim_pos : 0 < Module.finrank (AlgebraicClosure K1) (π i) := by
    let τ : Rep (AlgebraicClosure K1) H := Rep.of (π i).ρ
    letI : τ.ρ.IsIrreducible := by
      simpa [τ] using (FDRep.isIrreducible_of_simple (π i))
    -- The basis constituent is a genuine irreducible representation, so its degree is positive.
    have hτ_nontriv : Nontrivial τ := by
      -- An irreducible finite-dimensional representation cannot be the zero module.
      by_contra hτ_trivial
      letI : Subsingleton τ := not_nontrivial_iff_subsingleton.mp hτ_trivial
      have hbot : (⊥ : Subrepresentation τ.ρ) = ⊤ := by
        apply Subrepresentation.toSubmodule_injective
        ext x
        constructor
        · intro _
          trivial
        · intro _
          simpa using (Subsingleton.elim x 0)
      exact bot_ne_top hbot
    letI : Nontrivial τ := hτ_nontriv
    simpa [τ] using (Module.finrank_pos : 0 < Module.finrank (AlgebraicClosure K1) τ)
  have hpoint_i :
      χH 1 = (c i : AlgebraicClosure K1) * Module.finrank (AlgebraicClosure K1) (π i) := by
    have hsum_single :
        ∑ j, ((c j : AlgebraicClosure K1) * (π j).character 1) =
          (c i : AlgebraicClosure K1) * (π i).character 1 := by
      refine Finset.sum_eq_single i ?_ ?_
      · intro j _ hji
        simp [hzero j hji]
      · intro hi_not_mem
        exact False.elim (hi_not_mem (Finset.mem_univ i))
    calc
      χH 1 = (∑ j, c j • (π j).character) 1 := by
        symm
        exact congrFun hx 1
      _ = ∑ j, ((c j : AlgebraicClosure K1) * (π j).character 1) := by
            simp
      _ = (c i : AlgebraicClosure K1) * (π i).character 1 := hsum_single
      _ = (c i : AlgebraicClosure K1) * Module.finrank (AlgebraicClosure K1) (π i) := by
            simp
  have hi_one : c i = 1 := by
    rcases hi_sign with hi_one | hi_neg_one
    · exact hi_one
    · have hfield :
          (n : AlgebraicClosure K1) =
            ((- (Module.finrank (AlgebraicClosure K1) (π i) : ℤ)) : AlgebraicClosure K1) := by
        calc
          (n : AlgebraicClosure K1) = χH 1 := by
            simpa using hχH_one.symm
          _ = (c i : AlgebraicClosure K1) *
                Module.finrank (AlgebraicClosure K1) (π i) := hpoint_i
          _ = ((- (Module.finrank (AlgebraicClosure K1) (π i) : ℤ)) :
                AlgebraicClosure K1) := by
                simp [hi_neg_one]
      have hint :
          (n : ℤ) = - (Module.finrank (AlgebraicClosure K1) (π i) : ℤ) := by
        exact_mod_cast hfield
      have hn_pos_int : (0 : ℤ) < n := by
        exact_mod_cast hn_pos
      have hdim_pos_int : (0 : ℤ) < Module.finrank (AlgebraicClosure K1) (π i) := by
        exact_mod_cast hdim_pos
      linarith
  let τH : Rep (AlgebraicClosure K1) H := Rep.of (π i).ρ
  have hχH_eq :
      χH = τH.ρ.character := by
    ext h
    have hsum_single :
        ∑ x, ((c x : AlgebraicClosure K1) * (π x).character h) = (π i).character h := by
      calc
        ∑ x, ((c x : AlgebraicClosure K1) * (π x).character h) =
            (c i : AlgebraicClosure K1) * (π i).character h := by
              refine Finset.sum_eq_single i ?_ ?_
              · intro j _ hji
                simp [hzero j hji]
              · intro hi_not_mem
                exact False.elim (hi_not_mem (Finset.mem_univ i))
        _ = (π i).character h := by
              simp [hi_one]
    calc
      χH h = (∑ j, c j • (π j).character) h := by
        symm
        exact congrFun hx h
      _ = ∑ x, ((c x : AlgebraicClosure K1) * (π x).character h) := by
            simp
      _ = τH.ρ.character h := by
            simpa [τH] using hsum_single
  let τρ : Representation (AlgebraicClosure K1) G τH := τH.ρ.comp e.symm.toMonoidHom
  have hτρ_irr : τρ.IsIrreducible := by
    letI : τH.ρ.IsIrreducible := by
      simpa [τH] using (FDRep.isIrreducible_of_simple (π i))
    simpa [τρ, τH] using
      (isIrreducible_comp_of_mulEquiv_field_local
        (G := G) (H := H) (L := AlgebraicClosure K1) (e := e.symm) (σ := τH.ρ))
  let τlift : Representation (AlgebraicClosure K1) G (ULift.{max u v} τH) :=
    ulift_carrier_representation_local τρ
  let τ : Rep.{max u v} (AlgebraicClosure K1) G := Rep.of τlift
  have hτ_irr : τ.ρ.IsIrreducible := by
    letI : τρ.IsIrreducible := hτρ_irr
    have hτlift_irr : τlift.IsIrreducible := by
      exact isIrreducible_of_nonempty_equiv
        ⟨Representation.Equiv.mk ULift.moduleEquiv.symm fun g => by
          ext x
          rfl⟩
    simpa [τ, τlift] using hτlift_irr
  have hτ_char : τ.ρ.character = χ := by
    ext g
    calc
      τ.ρ.character g = τlift.character g := rfl
      _ = τρ.character g := by
            simpa [τlift] using ulift_carrier_representation_character_apply_local τρ g
      _ = τH.ρ.character (e.symm g) := by
            rfl
      _ = χ g := by
            simpa [H, e, χH] using (congrFun hχH_eq (e.symm g)).symm
  refine ⟨τ, inferInstance, hτ_irr, hτ_char⟩

/-- Helper for Exercise 12-12.2-6: the automorphism transport of one visible packet constituent
is again one of the visible packet constituents in the same scaled packet. -/
theorem transported_character_eq_packet_constituent_of_scaled_packet_transport_local
    {K1 : Type v} [Field K1] [CharZero K1]
    (ρ : Rep K1 G)
    [FiniteDimensional K1 ρ]
    (n : ℕ+)
    {ι : Type*} [Fintype ι]
    (ψ : ι → Rep.{max u v} (AlgebraicClosure K1) G)
    (d e : ι → ℕ)
    (hd_pos : ∀ i, 0 < d i)
    (hψ_fd : ∀ i, FiniteDimensional (AlgebraicClosure K1) (ψ i))
    (hψ_pairwise : PairwiseNonisomorphic ψ)
    (hψ_irr : ∀ i, (ψ i).ρ.IsIrreducible)
    (he : ∀ i, d i = (n : ℕ) * e i)
    (hscaled_packet :
      ((IsScalarTower.toAlgHom ℤ K1 (AlgebraicClosure K1)).compLeft G)
          ((((n : ℕ) : K1)⁻¹) • ρ.ρ.character) =
        ∑ i, (e i : AlgebraicClosure K1) • (ψ i).ρ.character)
    (σ : (AlgebraicClosure K1) ≃ₐ[K1] (AlgebraicClosure K1))
    (i : ι) :
    ∃ j, (fun g ↦ σ ((ψ i).ρ.character g)) = (ψ j).ρ.character := by
  classical
  let χσ : G → AlgebraicClosure K1 := fun g ↦ σ ((ψ i).ρ.character g)
  let χscaled : G → AlgebraicClosure K1 :=
    ((IsScalarTower.toAlgHom ℤ K1 (AlgebraicClosure K1)).compLeft G)
      ((((n : ℕ) : K1)⁻¹) • ρ.ρ.character)
  letI : FiniteDimensional (AlgebraicClosure K1) (ψ i) := hψ_fd i
  letI : (ψ i).ρ.IsIrreducible := hψ_irr i
  have hχσ_mem : χσ ∈ R[AlgebraicClosure K1](G) := by
    -- Transporting a genuine irreducible character keeps it in the character ring.
    simpa [χσ] using
      transported_constituent_character_mem_characterRing_local
        (G := G) (ψ0 := ψ i) (σ := σ)
  have hχσ_pair :
      ⟪χσ, χσ⟫ = (1 : AlgebraicClosure K1) := by
    -- The transported constituent is still irreducible, so its self-pairing remains `1`.
    simpa [χσ] using
      transported_irreducible_character_self_pairing_eq_one_local
        (G := G) (ψ0 := ψ i) (σ := σ)
  have hψi_dim_pos : 0 < Module.finrank (AlgebraicClosure K1) (ψ i) := by
    -- The irreducible constituent has positive degree, providing the positive value at `1`.
    exact irreducible_rep_finrank_pos_local (G := G) (V := ψ i)
  have hχσ_one :
      χσ 1 = (Module.finrank (AlgebraicClosure K1) (ψ i) : AlgebraicClosure K1) := by
    -- Evaluating the transported character at `1` reads off the same positive degree.
    simp [χσ, Representation.char_one]
  obtain ⟨τ, hτ_fd, hτ_irr, hτ_char⟩ :=
    exists_irreducible_rep_character_eq_of_mem_characterRing_self_pairing_eq_one_local
      (G := G) (χ := χσ) hχσ_mem hχσ_pair
      (Module.finrank (AlgebraicClosure K1) (ψ i)) hψi_dim_pos hχσ_one
  letI : FiniteDimensional (AlgebraicClosure K1) τ := hτ_fd
  letI : τ.ρ.IsIrreducible := hτ_irr
  have hcard_ne : (Nat.card G : AlgebraicClosure K1) ≠ 0 := by
    exact Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  letI : Invertible (Nat.card G : AlgebraicClosure K1) := invertibleOfNonzero hcard_ne
  have hei_pos : 0 < e i := by
    -- Dividing the positive visible multiplicity `d i` by the canonical denominator keeps a
    -- positive quotient coefficient.
    exact visible_packet_quotient_coeff_pos_local (n := n) d e hd_pos he i
  have hei_ne : (e i : AlgebraicClosure K1) ≠ 0 := by
    exact Nat.cast_ne_zero.mpr (Nat.ne_of_gt hei_pos)
  have hpair_i :
      ⟪χscaled, (ψ i).ρ.character⟫ = (e i : AlgebraicClosure K1) := by
    -- Pairing the scaled packet with the original constituent reads off the quotient
    -- coefficient `e i`.
    exact
      scaled_packet_constituent_pairing_eq_coefficient_local
        (G := G) χscaled ψ e hψ_fd hψ_pairwise hψ_irr hscaled_packet i
  have hχscaled_fixed :
      ∀ g : G, σ (χscaled g) = χscaled g := by
    intro g
    -- The scaled source character is defined over `K1`, so every `K1`-automorphism fixes it.
    simp [χscaled, smul_eq_mul, map_mul]
  have hpair_tau :
      ⟪χscaled, τ.ρ.character⟫ = (e i : AlgebraicClosure K1) := by
    -- Apply `σ` to the known pairing against `ψ i`, rewrite the transported source character
    -- back to itself, and identify the transported constituent with `τ`.
    calc
      ⟪χscaled, τ.ρ.character⟫
          = ⟪χscaled, χσ⟫ := by
              rw [hτ_char]
      _ = ⟪(fun g ↦ σ (χscaled g)), fun g ↦ σ ((ψ i).ρ.character g)⟫ := by
            congr
            funext g
            exact (hχscaled_fixed g).symm
      _ = σ ⟪χscaled, (ψ i).ρ.character⟫ := by
            symm
            exact
              algEquiv_groupFunctionPairing_apply_local
                (G := G) (σ := σ) χscaled (ψ i).ρ.character
      _ = (e i : AlgebraicClosure K1) := by
            rw [hpair_i]
            simp
  have hpair_tau_ne : ⟪χscaled, τ.ρ.character⟫ ≠ (0 : AlgebraicClosure K1) := by
    -- The transported pairing equals the positive quotient coefficient `e i`.
    simpa [hpair_tau] using hei_ne
  have hexists_pair :
      ∃ j, ⟪(ψ j).ρ.character, τ.ρ.character⟫ ≠ (0 : AlgebraicClosure K1) := by
    by_contra hnone
    have hzero :
        ∀ j, ⟪(ψ j).ρ.character, τ.ρ.character⟫ = (0 : AlgebraicClosure K1) := by
      intro j
      exact not_not.mp (by simpa using Classical.not_exists_not.mp hnone j)
    have hsum_zero :
        ⟪χscaled, τ.ρ.character⟫ = (0 : AlgebraicClosure K1) := by
      calc
        ⟪χscaled, τ.ρ.character⟫
            = ⟪∑ j, (e j : AlgebraicClosure K1) • (ψ j).ρ.character,
                τ.ρ.character⟫ := by
                  rw [← hscaled_packet]
        _ = ∑ j, (e j : AlgebraicClosure K1) * ⟪(ψ j).ρ.character, τ.ρ.character⟫ := by
              simpa using
                groupFunctionPairing_sum_field_smul_left_universe_local
                  (K' := K1) (G := G) (s := Finset.univ)
                  (a := fun j ↦ (e j : AlgebraicClosure K1))
                  (χ := fun j ↦ (ψ j).ρ.character) τ.ρ.character
        _ = 0 := by simp [hzero]
    exact hpair_tau_ne hsum_zero
  rcases hexists_pair with ⟨j, hj⟩
  letI : FiniteDimensional (AlgebraicClosure K1) (ψ j) := hψ_fd j
  letI : (ψ j).ρ.IsIrreducible := hψ_irr j
  have hIso : Nonempty ((ψ j).ρ.Equiv τ.ρ) := by
    by_contra hnot
    have hpair_zero :
        ⟪(ψ j).ρ.character, τ.ρ.character⟫ = (0 : AlgebraicClosure K1) := by
      exact
        Representation.groupFunctionPairingOverField_character_eq_zero_of_not_isomorphic
          (K := AlgebraicClosure K1) (G := G) (ρ := (ψ j).ρ) (σ := τ.ρ) hnot
    exact hj hpair_zero
  rcases hIso with ⟨eIso⟩
  refine ⟨j, ?_⟩
  -- Nonzero pairing forces the transported constituent to be isomorphic to one packet member,
  -- and isomorphic irreducibles have the same character.
  calc
    (fun g ↦ σ ((ψ i).ρ.character g)) = τ.ρ.character := by
      simpa [χσ] using hτ_char.symm
    _ = (ψ j).ρ.character := by
      simpa using (Representation.char_iso eIso).symm

/-- Helper for Exercise 12-12.2-6: the transport of packet constituents by a base-field
automorphism is given by an honest permutation of the visible packet indices. -/
theorem packet_transport_perm_exists_local
    {K1 : Type v} [Field K1] [CharZero K1]
    (ρ : Rep K1 G)
    [FiniteDimensional K1 ρ]
    (n : ℕ+)
    {ι : Type*} [Fintype ι]
    (ψ : ι → Rep.{max u v} (AlgebraicClosure K1) G)
    (d e : ι → ℕ)
    (hd_pos : ∀ i, 0 < d i)
    (hψ_fd : ∀ i, FiniteDimensional (AlgebraicClosure K1) (ψ i))
    (hψ_pairwise : PairwiseNonisomorphic ψ)
    (hψ_irr : ∀ i, (ψ i).ρ.IsIrreducible)
    (he : ∀ i, d i = (n : ℕ) * e i)
    (hscaled_packet :
      ((IsScalarTower.toAlgHom ℤ K1 (AlgebraicClosure K1)).compLeft G)
          ((((n : ℕ) : K1)⁻¹) • ρ.ρ.character) =
        ∑ i, (e i : AlgebraicClosure K1) • (ψ i).ρ.character)
    (σ : (AlgebraicClosure K1) ≃ₐ[K1] (AlgebraicClosure K1)) :
    ∃ τ : Equiv.Perm ι, ∀ i : ι, ∀ g : G, σ ((ψ i).ρ.character g) = (ψ (τ i)).ρ.character g := by
  classical
  let f : ι → ι := fun i ↦ Classical.choose <|
    transported_character_eq_packet_constituent_of_scaled_packet_transport_local
      (G := G) (ρ := ρ) (n := n) (ψ := ψ) (d := d) (e := e)
      hd_pos hψ_fd hψ_pairwise hψ_irr he hscaled_packet σ i
  have hf :
      ∀ i, (fun g ↦ σ ((ψ i).ρ.character g)) = (ψ (f i)).ρ.character := by
    intro i
    exact Classical.choose_spec <|
      transported_character_eq_packet_constituent_of_scaled_packet_transport_local
        (G := G) (ρ := ρ) (n := n) (ψ := ψ) (d := d) (e := e)
        hd_pos hψ_fd hψ_pairwise hψ_irr he hscaled_packet σ i
  have hf_inj : Function.Injective f := by
    intro i j hij
    by_contra hne
    letI : FiniteDimensional (AlgebraicClosure K1) (ψ i) := hψ_fd i
    letI : (ψ i).ρ.IsIrreducible := hψ_irr i
    letI : FiniteDimensional (AlgebraicClosure K1) (ψ j) := hψ_fd j
    letI : (ψ j).ρ.IsIrreducible := hψ_irr j
    have hchar_eq : (ψ i).ρ.character = (ψ j).ρ.character := by
      funext g
      apply σ.injective
      calc
        σ ((ψ i).ρ.character g) = (ψ (f i)).ρ.character g := congrFun (hf i) g
        _ = (ψ (f j)).ρ.character g := by rw [hij]
        _ = σ ((ψ j).ρ.character g) := by
              symm
              exact congrFun (hf j) g
    have hself_i :
        ⟪(ψ i).ρ.character, (ψ i).ρ.character⟫ = (1 : AlgebraicClosure K1) := by
      -- The original irreducible constituent has the standard self-pairing value `1`.
      simpa using
        transported_irreducible_character_self_pairing_eq_one_local
          (G := G) (ψ0 := ψ i)
          (σ := (AlgEquiv.refl :
            (AlgebraicClosure K1) ≃ₐ[K1] (AlgebraicClosure K1)))
    have hpair_eq_one :
        ⟪(ψ i).ρ.character, (ψ j).ρ.character⟫ = (1 : AlgebraicClosure K1) := by
      rw [← hchar_eq]
      exact hself_i
    have hcard_ne : (Nat.card G : AlgebraicClosure K1) ≠ 0 := by
      exact Nat.cast_ne_zero.mpr Nat.card_pos.ne'
    letI : Invertible (Nat.card G : AlgebraicClosure K1) := invertibleOfNonzero hcard_ne
    have hnot :
        ¬ Nonempty ((ψ i).ρ.Equiv (ψ j).ρ) := by
      intro hIso
      apply hψ_pairwise hne
      rcases hIso with ⟨eIso⟩
      simpa using (show Nonempty (ψ i ≅ ψ j) from ⟨Rep.mkIso eIso⟩)
    have hpair_zero :
        ⟪(ψ i).ρ.character, (ψ j).ρ.character⟫ = (0 : AlgebraicClosure K1) := by
      exact
        Representation.groupFunctionPairingOverField_character_eq_zero_of_not_isomorphic
          (K := AlgebraicClosure K1) (G := G) (ρ := (ψ i).ρ) (σ := (ψ j).ρ) hnot
    have hone_zero : (1 : AlgebraicClosure K1) = 0 := by
      exact hpair_eq_one.symm.trans hpair_zero
    exact one_ne_zero hone_zero
  have hf_surj : Function.Surjective f := Finite.surjective_of_injective hf_inj
  let τ : Equiv.Perm ι := Equiv.ofBijective f ⟨hf_inj, hf_surj⟩
  refine ⟨τ, ?_⟩
  intro i g
  -- The injective choice map is a permutation on the finite packet, and its defining equality is
  -- exactly the transported-character identity.
  simpa [τ, f] using congrFun (hf i) g

end FieldPart

end Exercise_12_12_2_6

end Representation
