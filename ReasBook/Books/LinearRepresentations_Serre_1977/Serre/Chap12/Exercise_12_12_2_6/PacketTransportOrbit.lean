import LinearRepresentations_Serre_1977.Chap12.Exercise_12_12_2_6.CanonicalPacketFrontier

noncomputable section

open scoped BigOperators
open scoped Representation
open scoped Representation.ExternalTensor
open scoped SubgroupInduction

universe u v

namespace Representation

open CategoryTheory
open Exercise_12_12_2_6

attribute [local instance] ULift.algebra'

section FieldPart

variable {G : Type u} [Group G] [Finite G]

local instance instFintypeGExercise_12_12_2_6_packet_transport_orbit : Fintype G :=
  Fintype.ofFinite G

/-- Helper for Exercise 12-12.2-6: transporting one visible constituent by a base-field
automorphism lands back in the same visible packet. -/
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

/-- Helper for Exercise 12-12.2-6: the transport of visible packet constituents by a
base-field automorphism is organized by a permutation of the packet indices. -/
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
    -- Apply the field automorphism to the scaled packet identity and reindex along `τ`.
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
                    simpa using hfixed.symm
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

/-- Helper for Exercise 12-12.2-6: every algebraic-closure automorphism yields an honest packet
transport permutation, and the scaled packet keeps the quotient coefficients invariant along that
transport. -/
theorem scaled_packet_transport_with_coeff_invariance_local
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
    ∃ τ : Equiv.Perm ι,
      (∀ i : ι, ∀ g : G, σ ((ψ i).ρ.character g) = (ψ (τ i)).ρ.character g) ∧
      (∀ i, e (τ i) = e i) := by
  obtain ⟨τ, hchar⟩ :=
    packet_transport_perm_exists_local
      (G := G) (ρ := ρ) (n := n) (ψ := ψ) (d := d) (e := e)
      hd_pos hψ_fd hψ_pairwise hψ_irr he hscaled_packet σ
  refine ⟨τ, hchar, ?_⟩
  -- Once the packet transport is realized by a permutation, the scaled packet identity forces
  -- the quotient coefficient to stay unchanged on that transported constituent.
  exact
    scaled_packet_coeff_transport_invariant_local
      (G := G) (ρ := ρ) (n := n) (ψ := ψ) (e := e)
      hψ_fd hψ_pairwise hψ_irr hscaled_packet σ τ hchar

/-- Helper for Exercise 12-12.2-6: if two visible constituents are connected by one algebraic
closure transport, then the scaled packet assigns them the same quotient coefficient. -/
theorem scaled_packet_coeff_eq_of_transport_relation_local
    {K1 : Type v} [Field K1] [CharZero K1]
    (ρ : Rep K1 G)
    [FiniteDimensional K1 ρ]
    (n : ℕ+)
    {ι : Type*} [Fintype ι]
    (ψ : ι → Rep.{max u v} (AlgebraicClosure K1) G)
    (d e : ι → ℕ)
    (_hd_pos : ∀ i, 0 < d i)
    (hψ_fd : ∀ i, FiniteDimensional (AlgebraicClosure K1) (ψ i))
    (hψ_pairwise : PairwiseNonisomorphic ψ)
    (hψ_irr : ∀ i, (ψ i).ρ.IsIrreducible)
    (_he : ∀ i, d i = (n : ℕ) * e i)
    (hscaled_packet :
      ((IsScalarTower.toAlgHom ℤ K1 (AlgebraicClosure K1)).compLeft G)
          ((((n : ℕ) : K1)⁻¹) • ρ.ρ.character) =
        ∑ i, (e i : AlgebraicClosure K1) • (ψ i).ρ.character)
    {i j : ι}
    (htransport :
      ∃ (σ : (AlgebraicClosure K1) ≃ₐ[K1] (AlgebraicClosure K1)) (τ : Equiv.Perm ι),
        (∀ k : ι, ∀ g : G, σ ((ψ k).ρ.character g) = (ψ (τ k)).ρ.character g) ∧
        τ i = j) :
    e j = e i := by
  rcases htransport with ⟨σ, τ, hchar, hij⟩
  -- Rewrite the target constituent as the transported image of `i`, then apply the transport
  -- invariance of the scaled packet coefficients.
  simpa [hij] using
    scaled_packet_coeff_transport_invariant_local
      (G := G) (ρ := ρ) (n := n) (ψ := ψ) (e := e)
      hψ_fd hψ_pairwise hψ_irr hscaled_packet σ τ hchar i

/-- Helper for Exercise 12-12.2-6: if one visible constituent reaches every other constituent by
one transport, then the scaled packet coefficients are already constant across the whole packet. -/
theorem common_coeff_of_full_transport_image_local
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
    (i0 : ι)
    (hcover :
      ∀ j : ι,
        ∃ (σ : (AlgebraicClosure K1) ≃ₐ[K1] (AlgebraicClosure K1)) (τ : Equiv.Perm ι),
          (∀ k : ι, ∀ g : G, σ ((ψ k).ρ.character g) = (ψ (τ k)).ρ.character g) ∧
          τ i0 = j) :
    ∀ i j, e i = e j := by
  intro i j
  have hi : e i = e i0 := by
    -- Reach `i` from the base constituent and compare the transported coefficient.
    exact
      scaled_packet_coeff_eq_of_transport_relation_local
        (G := G) (ρ := ρ) (n := n) (ψ := ψ) (d := d) (e := e)
        hd_pos hψ_fd hψ_pairwise hψ_irr he hscaled_packet
        (i := i0) (j := i) (htransport := hcover i)
  have hj : e j = e i0 := by
    -- The same transport argument reaches `j`, so both coefficients agree with the base one.
    exact
      scaled_packet_coeff_eq_of_transport_relation_local
        (G := G) (ρ := ρ) (n := n) (ψ := ψ) (d := d) (e := e)
        hd_pos hψ_fd hψ_pairwise hψ_irr he hscaled_packet
        (i := i0) (j := j) (htransport := hcover j)
  exact hi.trans hj.symm

/-- Helper for Exercise 12-12.2-6: the identity transport keeps the chosen base constituent
inside its own packet orbit. -/
theorem packet_transport_reaches_self_local
    {K1 : Type v} [Field K1] [CharZero K1]
    {ι : Type*}
    (ψ : ι → Rep.{max u v} (AlgebraicClosure K1) G)
    (i0 : ι) :
    ∃ (σ : (AlgebraicClosure K1) ≃ₐ[K1] (AlgebraicClosure K1)) (τ : Equiv.Perm ι),
      (∀ k : ι, ∀ g : G, σ ((ψ k).ρ.character g) = (ψ (τ k)).ρ.character g) ∧
      τ i0 = i0 := by
  -- The identity automorphism and the identity permutation give the trivial transport witness.
  refine
    ⟨(AlgEquiv.refl : (AlgebraicClosure K1) ≃ₐ[K1] (AlgebraicClosure K1)),
      (1 : Equiv.Perm ι), ?_, ?_⟩
  · intro k g
    rfl
  · rfl

/-- Helper for Exercise 12-12.2-6: packet-transport witnesses compose along Serre's visible
packet relation. -/
theorem packet_transport_relation_comp_local
    {K1 : Type v} [Field K1] [CharZero K1]
    {ι : Type*}
    (ψ : ι → Rep.{max u v} (AlgebraicClosure K1) G)
    {i j k : ι}
    (hij :
      ∃ (σ : (AlgebraicClosure K1) ≃ₐ[K1] (AlgebraicClosure K1)) (τ : Equiv.Perm ι),
        (∀ l : ι, ∀ g : G, σ ((ψ l).ρ.character g) = (ψ (τ l)).ρ.character g) ∧
        τ i = j)
    (hjk :
      ∃ (σ : (AlgebraicClosure K1) ≃ₐ[K1] (AlgebraicClosure K1)) (τ : Equiv.Perm ι),
        (∀ l : ι, ∀ g : G, σ ((ψ l).ρ.character g) = (ψ (τ l)).ρ.character g) ∧
        τ j = k) :
    ∃ (σ : (AlgebraicClosure K1) ≃ₐ[K1] (AlgebraicClosure K1)) (τ : Equiv.Perm ι),
      (∀ l : ι, ∀ g : G, σ ((ψ l).ρ.character g) = (ψ (τ l)).ρ.character g) ∧
      τ i = k := by
  rcases hij with ⟨σ₁, τ₁, hchar₁, hij⟩
  rcases hjk with ⟨σ₂, τ₂, hchar₂, hjk⟩
  refine ⟨σ₁.trans σ₂, τ₁.trans τ₂, ?_, by simp [hij, hjk]⟩
  intro l g
  -- Apply the first transport and then the second one on the transported constituent.
  calc
    (σ₁.trans σ₂) ((ψ l).ρ.character g) = σ₂ (σ₁ ((ψ l).ρ.character g)) := rfl
    _ = σ₂ ((ψ (τ₁ l)).ρ.character g) := by rw [hchar₁ l g]
    _ = (ψ (τ₂ (τ₁ l))).ρ.character g := by rw [hchar₂ (τ₁ l) g]
    _ = (ψ ((τ₁.trans τ₂) l)).ρ.character g := rfl

/-- Helper for Exercise 12-12.2-6: inverting a packet transport inverts both the automorphism and
the packet permutation. -/
theorem packet_transport_relation_symm_local
    {K1 : Type v} [Field K1] [CharZero K1]
    {ι : Type*}
    (ψ : ι → Rep.{max u v} (AlgebraicClosure K1) G)
    {i j : ι}
    (hij :
      ∃ (σ : (AlgebraicClosure K1) ≃ₐ[K1] (AlgebraicClosure K1)) (τ : Equiv.Perm ι),
        (∀ l : ι, ∀ g : G, σ ((ψ l).ρ.character g) = (ψ (τ l)).ρ.character g) ∧
        τ i = j) :
    ∃ (σ : (AlgebraicClosure K1) ≃ₐ[K1] (AlgebraicClosure K1)) (τ : Equiv.Perm ι),
      (∀ l : ι, ∀ g : G, σ ((ψ l).ρ.character g) = (ψ (τ l)).ρ.character g) ∧
      τ j = i := by
  rcases hij with ⟨σ, τ, hchar, hij⟩
  refine ⟨σ.symm, τ.symm, ?_, ?_⟩
  · intro l g
    -- Apply the inverse automorphism to the transport identity on `τ.symm l`.
    have htransport' :
        σ.symm ((ψ (τ (τ.symm l))).ρ.character g) =
          (ψ (τ.symm l)).ρ.character g := by
      simpa using (congrArg σ.symm (hchar (τ.symm l) g)).symm
    calc
      σ.symm ((ψ l).ρ.character g) = σ.symm ((ψ (τ (τ.symm l))).ρ.character g) := by
        exact congrArg (fun m : ι ↦ σ.symm ((ψ m).ρ.character g))
          (τ.apply_symm_apply l).symm
      _ = (ψ (τ.symm l)).ρ.character g := htransport'
  · rw [← hij]
    simp

end FieldPart

end Representation
