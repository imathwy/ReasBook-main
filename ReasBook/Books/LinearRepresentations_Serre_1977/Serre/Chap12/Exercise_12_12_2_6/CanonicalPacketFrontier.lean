import LinearRepresentations_Serre_1977.Chap01.Definition_1_1_2_1
import LinearRepresentations_Serre_1977.Chap02.Proposition_2_2_2_1
import LinearRepresentations_Serre_1977.Chap03.Theorem_3_3_2_1
import LinearRepresentations_Serre_1977.Chap06.Corollary_6_6_5_4
import LinearRepresentations_Serre_1977.Chap06.Proposition_6_6_5_5
import LinearRepresentations_Serre_1977.Chap10.Theorem_10_10_5_2
import LinearRepresentations_Serre_1977.Chap12.CharacterRingOverFieldScalarExtension
import LinearRepresentations_Serre_1977.Chap12.Exercise_12_12_2_3.API
import LinearRepresentations_Serre_1977.Chap12.Exercise_12_12_2_6.CharacterBasisCoefficients
import LinearRepresentations_Serre_1977.Chap12.Exercise_12_12_2_6.ComplexMinimalRealization
import LinearRepresentations_Serre_1977.Chap12.Exercise_12_12_2_6.ExternalTensorUniverseBridge
import LinearRepresentations_Serre_1977.Chap12.Exercise_12_12_2_6.FieldDenominatorDescent
import LinearRepresentations_Serre_1977.Chap12.Exercise_12_12_2_6.FieldDenominatorPrelude
import LinearRepresentations_Serre_1977.Chap12.Exercise_12_12_2_6.FieldTensorCenterBridge
import LinearRepresentations_Serre_1977.Chap12.Exercise_12_12_2_6.PacketCenterDescentCore
import LinearRepresentations_Serre_1977.Chap12.Exercise_12_12_2_6.PacketTransport
import LinearRepresentations_Serre_1977.Chap12.Exercise_12_12_2_6.ScalarExtensionConstituents
import LinearRepresentations_Serre_1977.Chap12.Exercise_12_12_2_6.ScalarExtensionPackets
import LinearRepresentations_Serre_1977.Chap12.Exercise_12_12_2_6.ScalarExtensionPairing

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

local instance instFintypeGExercise_12_12_2_6_canonical_packet_frontier : Fintype G :=
  Fintype.ofFinite G

/-- Helper for Exercise 12-12.2-6: the visible scalar-extension packet for the canonical
denominator reduces the source proof to the single remaining orbit/stabilizer descent step. -/
theorem canonical_scaled_character_visible_packet_frontier_local
    {K1 : Type v} [Field K1] [CharZero K1]
    (ρ : Rep K1 G)
    [ρ.ρ.IsIrreducible]
    (n : ℕ+)
    (hcanon : ((((n : ℕ) : K1)⁻¹) • ρ.ρ.character) ∈ R̄[K1](G))
    (_hmax :
      ∀ d : ℕ+, ((((d : ℕ) : K1)⁻¹) • ρ.ρ.character) ∈ R̄[K1](G) → d ≤ n) :
    ∃ (ι : Type) (_ : Fintype ι)
      (ψ : ι → Rep.{max u v} (AlgebraicClosure K1) G) (d e : ι → ℕ),
      (∀ i, 0 < d i) ∧
      (∀ i, FiniteDimensional (AlgebraicClosure K1) (ψ i)) ∧
      PairwiseNonisomorphic ψ ∧
      (∀ i, (ψ i).ρ.IsIrreducible) ∧
      ((IsScalarTower.toAlgHom ℤ K1 (AlgebraicClosure K1)).compLeft G) ρ.ρ.character =
        ∑ i, (d i : AlgebraicClosure K1) • (ψ i).ρ.character ∧
      (∀ i, (n : ℕ) ∣ d i) ∧
      (∀ i, d i = (n : ℕ) * e i) ∧
      ((IsScalarTower.toAlgHom ℤ K1 (AlgebraicClosure K1)).compLeft G)
          ((((n : ℕ) : K1)⁻¹) • ρ.ρ.character) =
        ∑ i, (e i : AlgebraicClosure K1) • (ψ i).ρ.character := by
  classical
  letI : FiniteDimensional K1 ρ :=
    Representation.IsIrreducible.finiteDimensional_of_finite ρ.ρ
  obtain ⟨ι, _, ψ, d, hd_pos, hψ_fd, hψ_pairwise, hψ_irr, hpacket⟩ :=
    scalar_extension_public_packet_visible_adapter_local
      (G := G) (K' := K1) ρ
  have hcoeff_div : ∀ i, (n : ℕ) ∣ d i := by
    -- The visible packet is now in the exact source-facing form required by the coefficient
    -- divisibility lemma.
    exact
      canonical_denominator_dvd_packet_coefficient_universe_local
        (G := G) (ρ := ρ) (n := n) hcanon
        (ψ := ψ) (d := d) hψ_fd hψ_pairwise hψ_irr hpacket
  choose e he using hcoeff_div
  have hcoeff_div' : ∀ i, (n : ℕ) ∣ d i := by
    intro i
    exact ⟨e i, he i⟩
  have hscaled_packet :
      ((IsScalarTower.toAlgHom ℤ K1 (AlgebraicClosure K1)).compLeft G)
          ((((n : ℕ) : K1)⁻¹) • ρ.ρ.character) =
        ∑ i, (e i : AlgebraicClosure K1) • (ψ i).ρ.character := by
    -- Divide the visible packet coefficients by the canonical denominator termwise.
    ext g
    have hn_ne : ((n : ℕ) : AlgebraicClosure K1) ≠ 0 := Nat.cast_ne_zero.mpr n.2.ne'
    calc
      ((IsScalarTower.toAlgHom ℤ K1 (AlgebraicClosure K1)).compLeft G)
          ((((n : ℕ) : K1)⁻¹) • ρ.ρ.character) g
          = (((n : ℕ) : AlgebraicClosure K1)⁻¹) *
              (((IsScalarTower.toAlgHom ℤ K1 (AlgebraicClosure K1)).compLeft G)
                ρ.ρ.character g) := by
                  simp [smul_eq_mul, map_mul]
      _ = (((n : ℕ) : AlgebraicClosure K1)⁻¹) *
            ((∑ i, (d i : AlgebraicClosure K1) • (ψ i).ρ.character) g) := by
              rw [hpacket]
      _ = (∑ i, (e i : AlgebraicClosure K1) • (ψ i).ρ.character) g := by
            simp [smul_eq_mul, Finset.mul_sum, he, hn_ne, mul_assoc, mul_left_comm, mul_comm]
  -- Package the visible packet, the quotient coefficients, and the scaled packet identity
  -- together so the later orbit/stabilizer descent can work at exactly Serre's frontier.
  exact
    ⟨ι, inferInstance, ψ, d, e, hd_pos, hψ_fd, hψ_pairwise, hψ_irr, hpacket, hcoeff_div', he,
      hscaled_packet⟩

/-- Helper for Exercise 12-12.2-6: once the visible packet already has common coefficient `n`,
dividing by `n` and reindexing along `Fin` gives the multiplicity-free packet used in the final
center-index step. -/
theorem canonical_scaled_character_packet_of_public_common_coeff_shadow_local
    {K1 : Type v} [Field K1] [CharZero K1]
    (ρ : Rep K1 G)
    [ρ.ρ.IsIrreducible]
    (n : ℕ+)
    {ι : Type*} [Fintype ι]
    (ψ : ι → Rep.{max u v} (AlgebraicClosure K1) G)
    (hψ_fd : ∀ i, FiniteDimensional (AlgebraicClosure K1) (ψ i))
    (hψ_pairwise : PairwiseNonisomorphic ψ)
    (hψ_irr : ∀ i, (ψ i).ρ.IsIrreducible)
    (hpacket :
      ((IsScalarTower.toAlgHom ℤ K1 (AlgebraicClosure K1)).compLeft G) ρ.ρ.character =
        ∑ i, (n : AlgebraicClosure K1) • (ψ i).ρ.character)
    (hψ_degree : ∀ i, (n : ℕ) ∣ Module.finrank (AlgebraicClosure K1) (ψ i)) :
    ∃ (r : ℕ) (_ : 0 < r) (ψ' : Fin r → Rep.{max u v} (AlgebraicClosure K1) G),
      (∀ i, FiniteDimensional (AlgebraicClosure K1) (ψ' i)) ∧
      PairwiseNonisomorphic ψ' ∧
      (∀ i, (ψ' i).ρ.IsIrreducible) ∧
      ((IsScalarTower.toAlgHom ℤ K1 (AlgebraicClosure K1)).compLeft G)
          ((((n : ℕ) : K1)⁻¹) • ρ.ρ.character) =
        ∑ i, (ψ' i).ρ.character ∧
      ∀ i, (n : ℕ) ∣ Module.finrank (AlgebraicClosure K1) (ψ' i) := by
  classical
  letI : FiniteDimensional K1 ρ :=
    Representation.IsIrreducible.finiteDimensional_of_finite ρ.ρ
  have hρ_nontriv : Nontrivial ρ := by
    -- An irreducible representation cannot have trivial carrier, or else `⊥ = ⊤`.
    by_contra hρ_trivial
    letI : Subsingleton ρ := not_nontrivial_iff_subsingleton.mp hρ_trivial
    have hbot : (⊥ : Subrepresentation ρ.ρ) = ⊤ := by
      apply Subrepresentation.toSubmodule_injective
      ext x
      constructor
      · intro _
        trivial
      · intro _
        simpa using (Subsingleton.elim x 0)
    exact bot_ne_top hbot
  have hι_nonempty : Nonempty ι := by
    -- Evaluating the public packet at `1` rules out the empty packet case.
    by_contra hι
    letI : IsEmpty ι := not_nonempty_iff.mp hι
    have hdim_ne :
        algebraMap K1 (AlgebraicClosure K1) (Module.finrank K1 ρ) ≠ 0 := by
      exact Nat.cast_ne_zero.mpr ((Module.finrank_pos_iff.mpr hρ_nontriv).ne')
    have hzero :
        algebraMap K1 (AlgebraicClosure K1) (Module.finrank K1 ρ) = 0 := by
      simpa [Representation.char_one] using congrFun hpacket 1
    exact hdim_ne hzero
  let r : ℕ := Fintype.card ι
  have hr : 0 < r := by
    simpa [r] using Fintype.card_pos_iff.mpr hι_nonempty
  let e : Fin r ≃ ι := (Fintype.equivFin ι).symm
  let ψ' : Fin r → Rep.{max u v} (AlgebraicClosure K1) G := fun i ↦ ψ (e i)
  have hψ'_fd : ∀ i, FiniteDimensional (AlgebraicClosure K1) (ψ' i) := by
    intro i
    simpa [ψ'] using hψ_fd (e i)
  have hψ'_pairwise : PairwiseNonisomorphic ψ' := by
    intro i j hij hIso
    apply hψ_pairwise (show e i ≠ e j from fun h => hij (e.injective h))
    simpa [ψ'] using hIso
  have hψ'_irr : ∀ i, (ψ' i).ρ.IsIrreducible := by
    intro i
    simpa [ψ'] using hψ_irr (e i)
  have hscaled_packet :
      ((IsScalarTower.toAlgHom ℤ K1 (AlgebraicClosure K1)).compLeft G)
          ((((n : ℕ) : K1)⁻¹) • ρ.ρ.character) =
        ∑ i, (ψ i).ρ.character := by
    -- Divide the common coefficient `n` out of the visible packet term by term.
    ext g
    have hn_ne : ((n : ℕ) : AlgebraicClosure K1) ≠ 0 := Nat.cast_ne_zero.mpr n.2.ne'
    calc
      ((IsScalarTower.toAlgHom ℤ K1 (AlgebraicClosure K1)).compLeft G)
          ((((n : ℕ) : K1)⁻¹) • ρ.ρ.character) g
          = (((n : ℕ) : AlgebraicClosure K1)⁻¹) *
              (((IsScalarTower.toAlgHom ℤ K1 (AlgebraicClosure K1)).compLeft G)
                ρ.ρ.character g) := by
                  simp [smul_eq_mul, map_mul]
      _ = (((n : ℕ) : AlgebraicClosure K1)⁻¹) *
            ((∑ i, (n : AlgebraicClosure K1) • (ψ i).ρ.character) g) := by
              rw [hpacket]
      _ = (∑ i, (ψ i).ρ.character) g := by
            simp [smul_eq_mul, Finset.mul_sum, hn_ne]
  have hscaled_packet' :
      ((IsScalarTower.toAlgHom ℤ K1 (AlgebraicClosure K1)).compLeft G)
          ((((n : ℕ) : K1)⁻¹) • ρ.ρ.character) =
        ∑ i, (ψ' i).ρ.character := by
    -- Reindex the finite packet along the explicit `Fin r` owner used by the main theorem.
    calc
      ((IsScalarTower.toAlgHom ℤ K1 (AlgebraicClosure K1)).compLeft G)
          ((((n : ℕ) : K1)⁻¹) • ρ.ρ.character)
          = ∑ i, (ψ i).ρ.character := hscaled_packet
      _ = ∑ i, (ψ' i).ρ.character := by
            symm
            exact Fintype.sum_equiv e (fun i : Fin r ↦ (ψ' i).ρ.character)
              (fun i : ι ↦ (ψ i).ρ.character) (by
                intro i
                simp [ψ'])
  -- The remainder is now only bookkeeping: the packet already has the target shape after
  -- rescaling and `Fin`-reindexing.
  refine ⟨r, hr, ψ', hψ'_fd, hψ'_pairwise, hψ'_irr, hscaled_packet', ?_⟩
  intro i
  simpa [ψ'] using hψ_degree (e i)

/-- Helper for Exercise 12-12.2-6: once the quotient coefficients have collapsed to `1`, the
visible packet is exactly the multiplicity-free packet used in the center-index argument. -/
theorem canonical_scaled_character_packet_of_scaled_visible_packet_coeff_one_shadow_local
    {K1 : Type v} [Field K1] [CharZero K1]
    (ρ : Rep K1 G)
    [ρ.ρ.IsIrreducible]
    (n : ℕ+)
    {ι : Type*} [Fintype ι]
    (ψ : ι → Rep.{max u v} (AlgebraicClosure K1) G)
    (d e : ι → ℕ)
    (hψ_fd : ∀ i, FiniteDimensional (AlgebraicClosure K1) (ψ i))
    (hψ_pairwise : PairwiseNonisomorphic ψ)
    (hψ_irr : ∀ i, (ψ i).ρ.IsIrreducible)
    (hpacket :
      ((IsScalarTower.toAlgHom ℤ K1 (AlgebraicClosure K1)).compLeft G) ρ.ρ.character =
        ∑ i, (d i : AlgebraicClosure K1) • (ψ i).ρ.character)
    (he : ∀ i, d i = (n : ℕ) * e i)
    (hcoeff_one : ∀ i, e i = 1)
    (hψ_degree : ∀ i, (n : ℕ) ∣ Module.finrank (AlgebraicClosure K1) (ψ i)) :
    ∃ (r : ℕ) (_ : 0 < r) (ψ' : Fin r → Rep.{max u v} (AlgebraicClosure K1) G),
      (∀ i, FiniteDimensional (AlgebraicClosure K1) (ψ' i)) ∧
      PairwiseNonisomorphic ψ' ∧
      (∀ i, (ψ' i).ρ.IsIrreducible) ∧
      ((IsScalarTower.toAlgHom ℤ K1 (AlgebraicClosure K1)).compLeft G)
          ((((n : ℕ) : K1)⁻¹) • ρ.ρ.character) =
        ∑ i, (ψ' i).ρ.character ∧
      ∀ i, (n : ℕ) ∣ Module.finrank (AlgebraicClosure K1) (ψ' i) := by
  have hpacket_common :
      ((IsScalarTower.toAlgHom ℤ K1 (AlgebraicClosure K1)).compLeft G) ρ.ρ.character =
        ∑ i, (n : AlgebraicClosure K1) • (ψ i).ρ.character := by
    -- Rewrite each raw multiplicity as the canonical denominator times the unit quotient.
    calc
      ((IsScalarTower.toAlgHom ℤ K1 (AlgebraicClosure K1)).compLeft G) ρ.ρ.character
          = ∑ i, (d i : AlgebraicClosure K1) • (ψ i).ρ.character := hpacket
      _ = ∑ i, (n : AlgebraicClosure K1) • (ψ i).ρ.character := by
            refine Finset.sum_congr rfl ?_
            intro i _
            have hdi : d i = (n : ℕ) := by
              calc
                d i = (n : ℕ) * e i := he i
                _ = (n : ℕ) * 1 := by rw [hcoeff_one i]
                _ = (n : ℕ) := Nat.mul_one _
            simp [hdi]
  -- Once the visible packet has common coefficient `n`, the remaining rescaling and reindexing is
  -- exactly the previous theorem.
  exact
    canonical_scaled_character_packet_of_public_common_coeff_shadow_local
      (G := G) (ρ := ρ) (n := n) (ψ := ψ)
      hψ_fd hψ_pairwise hψ_irr hpacket_common hψ_degree

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
    have hsum_zero : ∑ i, (c i) ^ 2 = 0 := by
      simp [hzero]
    linarith
  obtain ⟨i, hi_nonzero⟩ : ∃ i, c i ≠ 0 := by
    simpa [not_forall] using hnotallzero
  have hi_sq_le : (c i) ^ 2 ≤ 1 := by
    calc
      (c i) ^ 2 ≤ ∑ j, (c j) ^ 2 := by
        simpa using
          (Finset.single_le_sum (fun j _ ↦ sq_nonneg (c j)) (Finset.mem_univ i) :
            (c i) ^ 2 ≤ ∑ j, (c j) ^ 2)
      _ = 1 := h
  have hi_sq_eq : (c i) ^ 2 = 1 := by
    exact Int.sq_eq_one_of_sq_le_three (le_trans hi_sq_le (by norm_num)) hi_nonzero
  have hi_sign : c i = 1 ∨ c i = -1 := by
    exact sq_eq_one_iff.mp hi_sq_eq
  refine ⟨i, hi_sign, ?_⟩
  intro j hji
  have hsum_erase :
      Finset.sum (Finset.univ.erase i) (fun k ↦ (c k) ^ 2) + (c i) ^ 2 = 1 := by
    calc
      Finset.sum (Finset.univ.erase i) (fun k ↦ (c k) ^ 2) + (c i) ^ 2 = ∑ k, (c k) ^ 2 := by
        simpa using
          (Finset.sum_erase_add (s := Finset.univ) (f := fun k ↦ (c k) ^ 2)
            (Finset.mem_univ i))
      _ = 1 := h
  have herase_zero : Finset.sum (Finset.univ.erase i) (fun k ↦ (c k) ^ 2) = 0 := by
    linarith
  have hj_sq_le :
      (c j) ^ 2 ≤ Finset.sum (Finset.univ.erase i) (fun k ↦ (c k) ^ 2) := by
    have hj_mem : j ∈ Finset.univ.erase i := by
      simp [hji]
    simpa using
      (Finset.single_le_sum (fun k _ ↦ sq_nonneg (c k)) hj_mem :
        (c j) ^ 2 ≤ Finset.sum (Finset.univ.erase i) (fun k ↦ (c k) ^ 2))
  have hj_sq_eq_zero : (c j) ^ 2 = 0 := by
    have hj_sq_nonneg : 0 ≤ (c j) ^ 2 := sq_nonneg (c j)
    linarith
  exact sq_eq_zero_iff.mp hj_sq_eq_zero

/-- Helper for Exercise 12-12.2-6: the visible scalar-extension packet for the canonical
denominator reduces the source proof to the single remaining orbit/stabilizer descent step. -/
theorem visible_scaled_packet_coeff_one_of_common_coeff_local
    {K1 : Type v} [Field K1] [CharZero K1]
    (ρ : Rep K1 G)
    [ρ.ρ.IsIrreducible]
    [FiniteDimensional K1 ρ]
    (n : ℕ+)
    (hcanon : ((((n : ℕ) : K1)⁻¹) • ρ.ρ.character) ∈ R̄[K1](G))
    (hmax :
      ∀ d : ℕ+, ((((d : ℕ) : K1)⁻¹) • ρ.ρ.character) ∈ R̄[K1](G) → d ≤ n)
    {ι : Type*} [Fintype ι]
    (ψ : ι → Rep.{max u v} (AlgebraicClosure K1) G)
    (d e : ι → ℕ)
    (hd_pos : ∀ i, 0 < d i)
    (hψ_fd : ∀ i, FiniteDimensional (AlgebraicClosure K1) (ψ i))
    (_hψ_pairwise : PairwiseNonisomorphic ψ)
    (_hψ_irr : ∀ i, (ψ i).ρ.IsIrreducible)
    (hpacket :
      ((IsScalarTower.toAlgHom ℤ K1 (AlgebraicClosure K1)).compLeft G) ρ.ρ.character =
        ∑ i, (d i : AlgebraicClosure K1) • (ψ i).ρ.character)
    (he : ∀ i, d i = (n : ℕ) * e i)
    (hconst : ∀ i j, e i = e j) :
    ∀ i, e i = 1 := by
  intro i
  have hei_pos : 0 < e i := by
    -- Positivity of the visible packet multiplicity survives after dividing by the canonical
    -- denominator factor `n`.
    exact visible_packet_quotient_coeff_pos_local (n := n) d e hd_pos he i
  let m : ℕ+ := ⟨(n : ℕ) * e i, Nat.mul_pos n.pos hei_pos⟩
  have hm : ∀ j, (m : ℕ) ∣ d j := by
    intro j
    refine ⟨1, ?_⟩
    calc
      d j = (n : ℕ) * e j := he j
      _ = (n : ℕ) * e i := by rw [hconst j i]
      _ = (m : ℕ) * 1 := by simp [m, Nat.mul_comm]
  have hm_dvd_n : (m : ℕ) ∣ (n : ℕ) :=
    public_packet_common_divisor_dvd_canonical_denominator_local
      (G := G) (ρ := ρ) (n := n) hcanon hmax
      (m := m) (ψ := ψ) (d := d) hψ_fd hm hpacket
  rcases hm_dvd_n with ⟨k, hk⟩
  have hone : 1 = e i * k := by
    apply Nat.eq_of_mul_eq_mul_left n.pos
    calc
      (n : ℕ) * 1 = (n : ℕ) := by simp
      _ = (m : ℕ) * k := hk
      _ = ((n : ℕ) * e i) * k := by simp [m]
      _ = (n : ℕ) * (e i * k) := by ac_rfl
  exact Nat.eq_one_of_dvd_one ⟨k, hone⟩

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
    -- Over the algebraic closure, Schur's lemma makes the self-intertwining space
    -- one-dimensional.
    have hfinrank :
        Module.finrank (AlgebraicClosure K1)
            (Representation.IntertwiningMap (ψ j).ρ (ψ j).ρ) = 1 := by
      simpa using
        Representation.IsIrreducible.finrank_intertwiningMap_self (ρ := (ψ j).ρ)
    simpa [hfinrank] using
      (Representation.groupFunctionPairingOverField_character_eq_finrank_intertwiningMap
        (K := AlgebraicClosure K1) (G := G) (ρ := (ψ j).ρ) (σ := (ψ j).ρ))
  -- Expand the packet and kill every off-diagonal summand by orthogonality.
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

/-- Helper for Exercise 12-12.2-6: transporting an algebraic-closure character through a
base-field automorphism keeps it inside the algebraic-closure character ring. -/
theorem transported_constituent_character_mem_characterRing_local
    {K1 : Type v} [Field K1] [CharZero K1]
    (ψ0 : Rep.{max u v} (AlgebraicClosure K1) G)
    [FiniteDimensional (AlgebraicClosure K1) ψ0]
    (σ : (AlgebraicClosure K1) ≃ₐ[K1] (AlgebraicClosure K1)) :
    (fun g ↦ σ (ψ0.ρ.character g)) ∈ R[AlgebraicClosure K1](G) := by
  -- A field automorphism only changes coefficients, so it transports honest characters to
  -- honest characters over the same algebraically closed field.
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
  -- Push the automorphism through the scalar prefactor and the finite sum defining the pairing.
  rw [Representation.groupFunctionPairingOverField, Representation.groupFunctionPairingOverField]
  simp [map_mul, map_sum]

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
    -- The self-pairing computes the dimension of the self-intertwining space.
    have hfinrank :
        Module.finrank (AlgebraicClosure K1)
            (Representation.IntertwiningMap ψ0.ρ ψ0.ρ) = 1 := by
      simpa using Representation.IsIrreducible.finrank_intertwiningMap_self (ρ := ψ0.ρ)
    simpa [hfinrank] using
      (Representation.groupFunctionPairingOverField_character_eq_finrank_intertwiningMap
        (K := AlgebraicClosure K1) (G := G) (ρ := ψ0.ρ) (σ := ψ0.ρ))
  -- Apply the automorphism to the standard self-pairing formula and simplify.
  calc
    ⟪(fun g ↦ σ (ψ0.ρ.character g)), fun g ↦ σ (ψ0.ρ.character g)⟫
        = σ ⟪ψ0.ρ.character, ψ0.ρ.character⟫ := by
            symm
            exact
              algEquiv_groupFunctionPairing_apply_local
                (G := G) (σ := σ) ψ0.ρ.character ψ0.ρ.character
    _ = σ (1 : AlgebraicClosure K1) := by rw [hself]
    _ = 1 := by simp

/-- Helper for Exercise 12-12.2-6: over the algebraic closure, a character-ring element with
self-pairing `1` and positive value at `1` is already the character of one irreducible
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
  have hII : ∀ (i1 : Fintype H) (φ' ψ' : H → AlgebraicClosure K1),
      @Representation.groupFunctionPairingOverField (AlgebraicClosure K1) H _ _ i1 φ' ψ' =
        @Representation.groupFunctionPairingOverField (AlgebraicClosure K1) H _ _
          (Fintype.ofFinite H) φ' ψ' :=
    fun i1 φ' ψ' => by rw [Subsingleton.elim i1 (Fintype.ofFinite H)]
  have hχH : χH ∈ R[AlgebraicClosure K1](H) := by
    -- Move the character-ring element to the same-universe owner needed for the irreducible
    -- basis argument.
    simpa [H, e, χH] using
      (mem_characterRingOverField_precomp_mulEquiv_local
        (K' := AlgebraicClosure K1) (G₀ := G) (H := H) (e := e) (hχ := hχ))
  have hpairH : ⟪χH, χH⟫ = (1 : AlgebraicClosure K1) := by
    -- The normalized pairing is invariant under precomposition by a multiplicative equivalence.
    simpa [χH, hII] using
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
    -- Expand `χH` in the irreducible-character basis over the algebraic closure.
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
    simpa [hfinrank, hII] using
      (Representation.groupFunctionPairingOverField_character_eq_finrank_intertwiningMap
        (K := AlgebraicClosure K1) (G := H) (ρ := (π i).ρ) (σ := (π i).ρ))
  have hcoeff_pair :
      ∀ i, ⟪χH, (π i).character⟫ = (c i : AlgebraicClosure K1) := by
    intro i
    calc
      ⟪χH, (π i).character⟫
          = (((c i : ℤ) : AlgebraicClosure K1) *
              ⟪(π i).character, (π i).character⟫) := by
                simpa [x, b, c, hII] using
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
            simpa [hII] using
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

/-- Helper for Exercise 12-12.2-6: a finite-dimensional irreducible constituent has positive
degree. -/
theorem irreducible_rep_finrank_pos_local
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

end FieldPart

end Representation
