import Mathlib
import LinearRepresentations_Serre_1977.Chap02.Proposition_2_2_2_1
import LinearRepresentations_Serre_1977.Chap03.Theorem_3_3_2_1
import LinearRepresentations_Serre_1977.Chap06.Corollary_6_6_5_4
import LinearRepresentations_Serre_1977.Chap06.Proposition_6_6_5_5
import LinearRepresentations_Serre_1977.Chap12.Exercise_12_12_2_3.API
import LinearRepresentations_Serre_1977.Chap12.Exercise_12_12_2_6.CharacterBasisCoefficients
import LinearRepresentations_Serre_1977.Chap12.Exercise_12_12_2_6.ComplexMinimalRealization
import LinearRepresentations_Serre_1977.Chap12.Exercise_12_12_2_6.FieldDenominatorDescent
import LinearRepresentations_Serre_1977.Chap12.Exercise_12_12_2_6.FieldTensorCenterBridge
import LinearRepresentations_Serre_1977.Chap12.Exercise_12_12_2_6.ScalarExtensionConstituents
import LinearRepresentations_Serre_1977.Chap12.Exercise_12_12_2_6.ScalarExtensionPairing
import LinearRepresentations_Serre_1977.Chap12.Proposition_12_12_2_1

noncomputable section

open scoped BigOperators
open scoped Representation
open scoped Representation.ExternalTensor
open scoped SubgroupInduction

universe u v w

namespace Representation

open CategoryTheory
open Exercise_12_12_2_6

attribute [local instance] ULift.algebra'

section FieldPart

variable {K : Type u} [Field K] [CharZero K]
variable {G : Type u} [Group G] [Finite G]

local instance instFintypeGExercise_12_12_2_6_packets : Fintype G := Fintype.ofFinite G
/-- Helper for Exercise 12-12.2-6: the normalized pairing is additive on finite
`AlgebraicClosure K'`-linear combinations in its left argument without requiring the field and the
group to live in the same universe. -/
theorem groupFunctionPairing_sum_field_smul_left_universe_local
    {K' : Type v} [Field K'] [CharZero K']
    {ι : Type*} (s : Finset ι) (a : ι → AlgebraicClosure K') (χ : ι → G → AlgebraicClosure K')
    (ψ : G → AlgebraicClosure K') :
    ⟪∑ j ∈ s, a j • χ j, ψ⟫ = ∑ j ∈ s, a j * ⟪χ j, ψ⟫ := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp [Representation.groupFunctionPairingOverField]
  | insert i s hi ih =>
      -- Expand the inserted scalar multiple and then apply the induction hypothesis.
      rw [Finset.sum_insert hi, Representation.groupFunctionPairing_add_left,
        Representation.groupFunctionPairing_smul_left, ih, Finset.sum_insert hi]

/-- Helper for Exercise 12-12.2-6: pairing a public algebraic-closure packet with one of its
irreducible constituents reads off exactly the corresponding packet coefficient. -/
theorem packet_constituent_pairing_eq_multiplicity_universe_local
    {K' : Type v} [Field K'] [CharZero K']
    (ρ : Rep K' G)
    [FiniteDimensional K' ρ]
    {ι : Type*} [Fintype ι]
    (ψ : ι → Rep.{max u v} (AlgebraicClosure K') G)
    (d : ι → ℕ)
    (hψ_fd : ∀ j, FiniteDimensional (AlgebraicClosure K') (ψ j))
    (hψ_pairwise : PairwiseNonisomorphic ψ)
    (hψ_irr : ∀ j, (ψ j).ρ.IsIrreducible)
    (hpacket :
      ((IsScalarTower.toAlgHom ℤ K' (AlgebraicClosure K')).compLeft G) ρ.ρ.character =
        ∑ j, (d j : AlgebraicClosure K') • (ψ j).ρ.character) :
    ∀ j,
      ⟪((IsScalarTower.toAlgHom ℤ K' (AlgebraicClosure K')).compLeft G) ρ.ρ.character,
        (ψ j).ρ.character⟫ = (d j : AlgebraicClosure K') := by
  intro j
  have hcard_ne : (Nat.card G : AlgebraicClosure K') ≠ 0 := by
    exact Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  letI : Invertible (Nat.card G : AlgebraicClosure K') := invertibleOfNonzero hcard_ne
  letI : FiniteDimensional (AlgebraicClosure K') (ψ j) := hψ_fd j
  letI : (ψ j).ρ.IsIrreducible := hψ_irr j
  have hself_pair :
      ⟪(ψ j).ρ.character, (ψ j).ρ.character⟫ = (1 : AlgebraicClosure K') := by
    have hfinrank :
        Module.finrank (AlgebraicClosure K')
            (Representation.IntertwiningMap (ψ j).ρ (ψ j).ρ) = 1 := by
      -- Over an algebraically closed field, Schur's lemma makes the self-intertwining space
      -- one-dimensional.
      simpa using
        Representation.IsIrreducible.finrank_intertwiningMap_self (ρ := (ψ j).ρ)
    simpa [hfinrank] using
      (Representation.groupFunctionPairingOverField_character_eq_finrank_intertwiningMap
        (K := AlgebraicClosure K') (G := G) (ρ := (ψ j).ρ) (σ := (ψ j).ρ))
  calc
    ⟪((IsScalarTower.toAlgHom ℤ K' (AlgebraicClosure K')).compLeft G) ρ.ρ.character,
        (ψ j).ρ.character⟫
        = ⟪∑ l, (d l : AlgebraicClosure K') • (ψ l).ρ.character,
            (ψ j).ρ.character⟫ := by
              rw [hpacket]
    _ = ∑ l, (d l : AlgebraicClosure K') * ⟪(ψ l).ρ.character, (ψ j).ρ.character⟫ := by
          simpa using
            groupFunctionPairing_sum_field_smul_left_universe_local
              (K' := K') (G := G) (s := Finset.univ)
              (a := fun l ↦ (d l : AlgebraicClosure K'))
              (χ := fun l ↦ (ψ l).ρ.character) ((ψ j).ρ.character)
    _ = (d j : AlgebraicClosure K') * ⟪(ψ j).ρ.character, (ψ j).ρ.character⟫ := by
          refine Finset.sum_eq_single j ?_ ?_
          · intro l _ hlj
            letI : FiniteDimensional (AlgebraicClosure K') (ψ l) := hψ_fd l
            letI : (ψ l).ρ.IsIrreducible := hψ_irr l
            have hnot :
                ¬ Nonempty ((ψ l).ρ.Equiv (ψ j).ρ) := by
              intro hIso
              apply hψ_pairwise hlj
              rcases hIso with ⟨e⟩
              simpa using (show Nonempty (ψ l ≅ ψ j) from ⟨Rep.mkIso e⟩)
            have hpair_zero :
                ⟪(ψ l).ρ.character, (ψ j).ρ.character⟫ = (0 : AlgebraicClosure K') := by
              exact
                Representation.groupFunctionPairingOverField_character_eq_zero_of_not_isomorphic
                  (K := AlgebraicClosure K') (G := G) (ρ := (ψ l).ρ) (σ := (ψ j).ρ) hnot
            rw [hpair_zero, mul_zero]
          · intro hj
            exact (hj (Finset.mem_univ j)).elim
    _ = d j := by
          rw [hself_pair]
          simp

/-- Helper for Exercise 12-12.2-6: once the canonical denominator `n` is fixed, every coefficient
in any public algebraic-closure packet decomposition is a multiple of `n`. -/
theorem canonical_denominator_dvd_packet_coefficient_universe_local
    {K' : Type v} [Field K'] [CharZero K']
    (ρ : Rep K' G)
    [ρ.ρ.IsIrreducible] [FiniteDimensional K' ρ]
    (n : ℕ+)
    (hcanon : ((((n : ℕ) : K')⁻¹) • ρ.ρ.character) ∈ R̄[K'](G))
    {ι : Type*} [Fintype ι]
    (ψ : ι → Rep.{max u v} (AlgebraicClosure K') G)
    (d : ι → ℕ)
    (hψ_fd : ∀ j, FiniteDimensional (AlgebraicClosure K') (ψ j))
    (hψ_pairwise : PairwiseNonisomorphic ψ)
    (hψ_irr : ∀ j, (ψ j).ρ.IsIrreducible)
    (hpacket :
      ((IsScalarTower.toAlgHom ℤ K' (AlgebraicClosure K')).compLeft G) ρ.ρ.character =
        ∑ j, (d j : AlgebraicClosure K') • (ψ j).ρ.character) :
    ∀ j, (n : ℕ) ∣ d j := by
  intro j
  have hscaled_closure :
      ((IsScalarTower.toAlgHom ℤ K' (AlgebraicClosure K')).compLeft G)
          ((((n : ℕ) : K')⁻¹) • ρ.ρ.character) ∈
        R[AlgebraicClosure K'](G) := by
    -- Repackage the source-side overline witness as an honest algebraic-closure character-ring
    -- element before pairing with the packet constituents.
    exact
      (mem_overlineCharacterRingInExtension_iff K' (AlgebraicClosure K')
        ((((n : ℕ) : K')⁻¹) • ρ.ρ.character)).1 hcanon
  obtain ⟨z, hz⟩ :
      ∃ z : ℤ,
        ⟪((IsScalarTower.toAlgHom ℤ K' (AlgebraicClosure K')).compLeft G)
            ((((n : ℕ) : K')⁻¹) • ρ.ρ.character),
          (ψ j).ρ.character⟫ = (z : AlgebraicClosure K') := by
    -- The canonically scaled source character lies in the algebraic-closure character ring, so
    -- its pairing with an irreducible constituent is integral.
    exact
      pairing_eq_int_of_mem_characterRingOverAlgClosure_local
        (G := G) (K' := K')
        ⟨_, hscaled_closure⟩ (σ := (ψ j).ρ)
  have hmap_scaled :
      ((IsScalarTower.toAlgHom ℤ K' (AlgebraicClosure K')).compLeft G)
          ((((n : ℕ) : K')⁻¹) • ρ.ρ.character) =
        ((((n : ℕ) : AlgebraicClosure K')⁻¹) •
          ((IsScalarTower.toAlgHom ℤ K' (AlgebraicClosure K')).compLeft G) ρ.ρ.character) := by
    -- The coefficient extension commutes with the scalar factor `1 / n`.
    ext g
    simp [smul_eq_mul, map_mul]
  have hpair_scaled :
      ⟪((IsScalarTower.toAlgHom ℤ K' (AlgebraicClosure K')).compLeft G)
            ((((n : ℕ) : K')⁻¹) • ρ.ρ.character),
          (ψ j).ρ.character⟫ =
        (((n : ℕ) : AlgebraicClosure K')⁻¹) * (d j : AlgebraicClosure K') := by
    -- Rewrite the scaled source character through the packet decomposition and read off the
    -- `j`-th packet coefficient.
    calc
      ⟪((IsScalarTower.toAlgHom ℤ K' (AlgebraicClosure K')).compLeft G)
            ((((n : ℕ) : K')⁻¹) • ρ.ρ.character),
          (ψ j).ρ.character⟫
          =
            ⟪((((n : ℕ) : AlgebraicClosure K')⁻¹) •
                ((IsScalarTower.toAlgHom ℤ K' (AlgebraicClosure K')).compLeft G) ρ.ρ.character),
              (ψ j).ρ.character⟫ := by
                rw [hmap_scaled]
      _ =
          (((n : ℕ) : AlgebraicClosure K')⁻¹) *
            ⟪((IsScalarTower.toAlgHom ℤ K' (AlgebraicClosure K')).compLeft G) ρ.ρ.character,
              (ψ j).ρ.character⟫ := by
                rw [Representation.groupFunctionPairing_smul_left]
      _ =
          (((n : ℕ) : AlgebraicClosure K')⁻¹) * (d j : AlgebraicClosure K') := by
                rw [packet_constituent_pairing_eq_multiplicity_universe_local
                  (G := G) (ρ := ρ) (ψ := ψ) (d := d) hψ_fd hψ_pairwise hψ_irr hpacket j]
  have hn_ne : ((n : ℕ) : AlgebraicClosure K') ≠ 0 := Nat.cast_ne_zero.mpr n.2.ne'
  have hmul :
      ((n : ℕ) : AlgebraicClosure K') * (z : AlgebraicClosure K') = (d j : AlgebraicClosure K') := by
    calc
      ((n : ℕ) : AlgebraicClosure K') * (z : AlgebraicClosure K')
          =
            ((n : ℕ) : AlgebraicClosure K') *
              ((((n : ℕ) : AlgebraicClosure K')⁻¹) * (d j : AlgebraicClosure K')) := by
                rw [← hz, hpair_scaled]
      _ = (d j : AlgebraicClosure K') := by
            field_simp [hn_ne]
  have hdivZ : ((n : ℤ) : ℤ) ∣ (d j : ℤ) := by
    refine ⟨z, ?_⟩
    exact_mod_cast hmul.symm
  exact Int.natCast_dvd_natCast.mp (by simpa using hdivZ)

/-- Helper for Exercise 12-12.2-6: any common divisor of the raw scalar-extension packet
coefficients already gives an admissible source denominator after mapping back from the algebraic
closure. -/
theorem common_divisor_of_scalar_extension_packet_coefficients_mem_overline_local
    {K' : Type v} [Field K'] [CharZero K']
    {ι : Type*} [Fintype ι]
    (ρ : Rep K' G)
    [ρ.ρ.IsIrreducible]
    (m : ℕ+)
    (ψ : ι → Rep.{max u v} (AlgebraicClosure K') G)
    (d : ι → ℕ)
    (hψ_fd : ∀ i, FiniteDimensional (AlgebraicClosure K') (ψ i))
    (hm : ∀ i, (m : ℕ) ∣ d i)
    (hpacket :
      ((IsScalarTower.toAlgHom ℤ K' (AlgebraicClosure K')).compLeft G) ρ.ρ.character =
        ∑ i, (d i : AlgebraicClosure K') • (ψ i).ρ.character) :
    ((((m : ℕ) : K')⁻¹) • ρ.ρ.character) ∈ R̄[K'](G) := by
  classical
  choose z hz using hm
  have hscaled_map :
      ((IsScalarTower.toAlgHom ℤ K' (AlgebraicClosure K')).compLeft G)
          ((((m : ℕ) : K')⁻¹) • ρ.ρ.character) =
        ((((m : ℕ) : AlgebraicClosure K')⁻¹) •
          ((IsScalarTower.toAlgHom ℤ K' (AlgebraicClosure K')).compLeft G) ρ.ρ.character) := by
    -- The coefficient extension commutes with the scalar factor `1 / m`.
    ext g
    simp [smul_eq_mul, map_mul]
  have hscaled_closure :
      ((IsScalarTower.toAlgHom ℤ K' (AlgebraicClosure K')).compLeft G)
          ((((m : ℕ) : K')⁻¹) • ρ.ρ.character) ∈
        R[AlgebraicClosure K'](G) := by
    rw [hscaled_map, hpacket]
    have hsum :
        ((((m : ℕ) : AlgebraicClosure K')⁻¹) •
            ∑ i, (d i : AlgebraicClosure K') • (ψ i).ρ.character) =
          ∑ i,
            ((((m : ℕ) : AlgebraicClosure K')⁻¹) •
              ((d i : AlgebraicClosure K') • (ψ i).ρ.character)) := by
      ext g
      simp [smul_eq_mul, Finset.mul_sum]
    rw [hsum]
    -- After dividing by the common divisor `m`, each packet coefficient becomes an integer.
    refine (R[AlgebraicClosure K'](G)).toSubmodule.sum_mem ?_
    intro i _
    have hzL : (d i : AlgebraicClosure K') = ((m : ℕ) : AlgebraicClosure K') * (z i : AlgebraicClosure K') := by
      exact_mod_cast hz i
    have hm_ne : ((m : ℕ) : AlgebraicClosure K') ≠ 0 := Nat.cast_ne_zero.mpr m.2.ne'
    have hterm :
        ((((m : ℕ) : AlgebraicClosure K')⁻¹) • ((d i : AlgebraicClosure K') • (ψ i).ρ.character)) =
          (z i : ℤ) • (ψ i).ρ.character := by
      ext g
      simp [smul_eq_mul, zsmul_eq_mul, hzL, hm_ne, mul_assoc, mul_left_comm, mul_comm]
    letI : FiniteDimensional (AlgebraicClosure K') (ψ i) := hψ_fd i
    simpa [hterm] using
      Submodule.smul_mem (R[AlgebraicClosure K'](G)).toSubmodule (z i : ℤ) (by
        simpa using
          Representation.rep_character_mem_characterRingOverField
            (K := AlgebraicClosure K') (G := G) (ψ i))
  exact
    (mem_overlineCharacterRingInExtension_iff K' (AlgebraicClosure K')
      ((((m : ℕ) : K')⁻¹) • ρ.ρ.character)).2 hscaled_closure

/-- Helper for Exercise 12-12.2-6: any common divisor of the public scalar-extension packet
coefficients already divides the canonical denominator `n`. -/
theorem public_packet_common_divisor_dvd_canonical_denominator_local
    {K' : Type v} [Field K'] [CharZero K']
    (ρ : Rep K' G)
    [ρ.ρ.IsIrreducible]
    (n : ℕ+)
    (hcanon : ((((n : ℕ) : K')⁻¹) • ρ.ρ.character) ∈ R̄[K'](G))
    (hmax :
      ∀ d : ℕ+, ((((d : ℕ) : K')⁻¹) • ρ.ρ.character) ∈ R̄[K'](G) → d ≤ n)
    {ι : Type*} [Fintype ι]
    (m : ℕ+)
    (ψ : ι → Rep.{max u v} (AlgebraicClosure K') G)
    (d : ι → ℕ)
    (hψ_fd : ∀ i, FiniteDimensional (AlgebraicClosure K') (ψ i))
    (hm : ∀ i, (m : ℕ) ∣ d i)
    (hpacket :
      ((IsScalarTower.toAlgHom ℤ K' (AlgebraicClosure K')).compLeft G) ρ.ρ.character =
        ∑ i, (d i : AlgebraicClosure K') • (ψ i).ρ.character) :
    (m : ℕ) ∣ (n : ℕ) := by
  have hm_overline :
      ((((m : ℕ) : K')⁻¹) • ρ.ρ.character) ∈ R̄[K'](G) := by
    -- First turn the common-divisor hypothesis on the packet coefficients into a source-side
    -- overline-character witness.
    exact
      common_divisor_of_scalar_extension_packet_coefficients_mem_overline_local
        (G := G) (ρ := ρ) (m := m) (ψ := ψ) (d := d) hψ_fd hm hpacket
  -- Then compare that admissible denominator with the maximal canonical one.
  exact
    scaled_character_denominator_dvd_canonical_denominator_local
      (G := G) (ρ := ρ) (hcanon := hcanon) (hmax := hmax) hm_overline

/-- Helper for Exercise 12-12.2-6: Proposition `12-12.2-1` already supplies the scalar-extension
packet for the same-universe lifted owner of `ρ`; the remaining work is only to descend that
packet back to the visible algebraic closure of `K'`. -/
theorem lifted_owner_scalar_extension_packet_local
    {K' : Type v} [Field K'] [CharZero K']
    (ρ : Rep K' G)
    [ρ.ρ.IsIrreducible] [FiniteDimensional K' ρ] :
    ∃ (ι : Type (max u v)) (_ : Fintype ι)
      (ψ : ι → Rep.{max u v} (AlgebraicClosure (ULift.{max u v} K')) (ULift.{max u v} G))
      (d : ι → ℕ),
      (∀ i, 0 < d i) ∧
      (∀ i, FiniteDimensional (AlgebraicClosure (ULift.{max u v} K')) (ψ i)) ∧
      PairwiseNonisomorphic ψ ∧
      (∀ i, (ψ i).ρ.IsIrreducible) ∧
      (Representation.scalarExtension
          (k := AlgebraicClosure (ULift.{max u v} K'))
          (lifted_field_basis_fdRep_local (L := K') (G0 := G) (V := ρ) ρ.ρ).ρ).character =
        ∑ i, (d i : AlgebraicClosure (ULift.{max u v} K')) • (ψ i).ρ.character := by
  -- Apply Proposition `12-12.2-1` to the lifted owner whose field and group already live in one
  -- common universe.
  simpa using
    (Representation.scalar_extension_character_eq_sum_irreducible_family_with_nat_coefficients
      (K := ULift.{max u v} K')
      (G := ULift.{max u v} G)
      (V := lifted_field_basis_fdRep_local (L := K') (G0 := G) (V := ρ) ρ.ρ))

/-- Helper for Exercise 12-12.2-6: the support-file packet theorem already gives the visible
algebraic-closure decomposition of `ρ`, so the main proof can stay on Serre's closure-first route
without reopening the lifted-owner transport. -/
theorem scalar_extension_public_packet_visible_adapter_local
    {K' : Type v} [Field K'] [CharZero K']
    (ρ : Rep K' G)
    [FiniteDimensional K' ρ] :
    ∃ (ι : Type) (_ : Fintype ι)
      (ψ : ι → Rep.{max u v} (AlgebraicClosure K') G)
      (d : ι → ℕ),
      (∀ i, 0 < d i) ∧
      (∀ i, FiniteDimensional (AlgebraicClosure K') (ψ i)) ∧
      PairwiseNonisomorphic ψ ∧
      (∀ i, (ψ i).ρ.IsIrreducible) ∧
      ((IsScalarTower.toAlgHom ℤ K' (AlgebraicClosure K')).compLeft G) ρ.ρ.character =
        ∑ i, (d i : AlgebraicClosure K') • (ψ i).ρ.character := by
  let e := (Module.finBasis K' ρ).equivFun
  let ρfin : Representation K' G (Fin (Module.finrank K' ρ) → K') :=
    { toFun := fun g ↦ e.conj (ρ.ρ g)
      map_one' := by
        calc
          e.conj (ρ.ρ 1) = e.conj 1 := by rw [map_one]
          _ = 1 := LinearEquiv.conj_id e
      map_mul' := by
        intro g h
        rw [map_mul]
        ext x
        simp [LinearEquiv.conj_apply_apply] }
  have hρfin_char : ρfin.character = ρ.ρ.character := by
    -- Move to coordinates only to place the carrier in the visible packet theorem's universe.
    ext g
    simpa [ρfin, Representation.character] using
      (LinearMap.trace_conj' (ρ.ρ g) e)
  let ρfinLift :
      Representation K' G (ULift.{max u v} (Fin (Module.finrank K' ρ) → K')) :=
    ulift_carrier_representation_local ρfin
  let τ : Rep.{max u v} K' G := Rep.of ρfinLift
  have hτ_char : τ.ρ.character = ρ.ρ.character := by
    -- The finite-basis model and the final carrier `ULift` preserve the same class function.
    ext g
    calc
      τ.ρ.character g = ρfin.character g := by
        simpa [τ, ρfinLift] using
          ulift_carrier_representation_character_apply_local (ρ := ρfin) g
      _ = ρ.ρ.character g := by
        simpa using congrFun hρfin_char g
  -- Route correction: use the visible packet produced in `ScalarExtensionConstituents` directly,
  -- then rewrite its scalar-extension character into the mapped source character.
  obtain ⟨ι, _, ψ, d, hd_pos, hψ_fd, hψ_pairwise, hψ_irr, hpacket⟩ :=
    Exercise_12_12_2_6.scalar_extension_public_packet_universe_local
      (G := G) (K := K') (τ := τ)
  refine ⟨ι, inferInstance, ψ, d, hd_pos, hψ_fd, hψ_pairwise, hψ_irr, ?_⟩
  -- The support-file theorem is stated for the scalar-extension character itself; the local map
  -- lemma converts it to the source-facing packet identity used in the main proof.
  simpa [τ, hτ_char, scalarExtension_character_eq_map_algClosure_local (G := G) (ρ := τ)] using
    hpacket

end FieldPart

end Representation
