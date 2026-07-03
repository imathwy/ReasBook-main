import Serre.Chap01.Definition_1_1_2_1
import Serre.Chap02.Proposition_2_2_2_1
import Serre.Chap03.Theorem_3_3_2_1
import Serre.Chap06.Corollary_6_6_5_4
import Serre.Chap06.Proposition_6_6_5_5
import Serre.Chap10.Theorem_10_10_5_2
import Serre.Chap12.CharacterRingOverFieldScalarExtension
import Serre.Chap12.Exercise_12_12_2_3.API
import Serre.Chap12.Exercise_12_12_2_6.CanonicalPacketCenterBridge
import Serre.Chap12.Exercise_12_12_2_6.CharacterBasisCoefficients
import Serre.Chap12.Exercise_12_12_2_6.ComplexMinimalRealization
import Serre.Chap12.Exercise_12_12_2_6.ExternalTensorUniverseBridge
import Serre.Chap12.Exercise_12_12_2_6.FieldDenominatorDescent
import Serre.Chap12.Exercise_12_12_2_6.FieldDenominatorPrelude
import Serre.Chap12.Exercise_12_12_2_6.FieldTensorCenterBridge
import Serre.Chap12.Exercise_12_12_2_6.PacketCenterDescentCore
import Serre.Chap12.Exercise_12_12_2_6.ScalarExtensionBlockProjectors
import Serre.Chap12.Exercise_12_12_2_6.ScalarExtensionConstituents
import Serre.Chap12.Exercise_12_12_2_6.ScalarExtensionPackets
import Serre.Chap12.Exercise_12_12_2_6.ScalarExtensionPairing

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped BigOperators
open scoped Representation
open scoped Representation.ExternalTensor
open scoped SubgroupInduction

scoped[Representation] notation:max "R(" G ")" => R[ℂ](G)

universe u v w

namespace Representation

open CategoryTheory
open Exercise_12_12_2_6

attribute [local instance] ULift.algebra'


section FieldPart

variable {K : Type u} [Field K] [CharZero K]
variable {G : Type u} [Group G] [Finite G]

local instance instFintypeGExercise_12_12_2_6_main : Fintype G := Fintype.ofFinite G

namespace Exercise_12_12_2_6

-- Route correction: the orbit-projector and stabilizer fixed-field descent frontiers are now
-- canonically owned by `ScalarExtensionBlockProjectors`. This target file reuses those imported
-- declarations directly so the remaining proof work stays in the theorem-local support owner.

end Exercise_12_12_2_6

/-- Helper for Exercise 12-12.2-6: the visible scalar-extension packet for the canonical
denominator reduces the source proof to the single remaining orbit/stabilizer descent step. -/
private theorem canonical_scaled_character_visible_packet_frontier_local
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
private theorem canonical_scaled_character_packet_of_public_common_coeff_shadow_local
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
private theorem canonical_scaled_character_packet_of_scaled_visible_packet_coeff_one_shadow_local
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
private theorem visible_packet_quotient_coeff_pos_local
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
private theorem integer_coefficients_eq_singleton_of_sq_sum_eq_one_local
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
private theorem visible_scaled_packet_coeff_one_of_common_coeff_local
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
private theorem scaled_packet_constituent_pairing_eq_coefficient_local
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
private theorem transported_constituent_character_mem_characterRing_local
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
private theorem algEquiv_groupFunctionPairing_apply_local
    {K1 : Type v} [Field K1] [CharZero K1]
    (σ : (AlgebraicClosure K1) ≃ₐ[K1] (AlgebraicClosure K1))
    (χ ψ : G → AlgebraicClosure K1) :
    σ ⟪χ, ψ⟫ = ⟪(fun g ↦ σ (χ g)), fun g ↦ σ (ψ g)⟫ := by
  -- Push the automorphism through the scalar prefactor and the finite sum defining the pairing.
  rw [Representation.groupFunctionPairingOverField, Representation.groupFunctionPairingOverField]
  simp [map_mul, map_sum]

/-- Helper for Exercise 12-12.2-6: transporting the character of an irreducible constituent
through a base-field automorphism preserves the self-pairing value `1`. -/
private theorem transported_irreducible_character_self_pairing_eq_one_local
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
private theorem exists_irreducible_rep_character_eq_of_mem_characterRing_self_pairing_eq_one_local
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

/-- Helper for Exercise 12-12.2-6: a finite-dimensional irreducible constituent has positive
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

/-- Helper for Exercise 12-12.2-6: transporting one visible constituent by a base-field
automorphism lands back in the same visible packet. -/
private theorem transported_character_eq_packet_constituent_of_scaled_packet_transport_local
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
private theorem packet_transport_perm_exists_local
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
private theorem scaled_packet_coeff_transport_invariant_local
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
private theorem scaled_packet_transport_with_coeff_invariance_local
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
private theorem scaled_packet_coeff_eq_of_transport_relation_local
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

/-- Helper for Exercise 12-12.2-6: once Serre's visible packet is one transport orbit, the
quotient coefficients are all `1`. -/
private theorem visible_scaled_packet_coeff_one_shadow_local
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
    (hψ_pairwise : PairwiseNonisomorphic ψ)
    (hψ_irr : ∀ i, (ψ i).ρ.IsIrreducible)
    (hpacket :
      ((IsScalarTower.toAlgHom ℤ K1 (AlgebraicClosure K1)).compLeft G) ρ.ρ.character =
        ∑ i, (d i : AlgebraicClosure K1) • (ψ i).ρ.character)
    (he : ∀ i, d i = (n : ℕ) * e i)
    (hscaled_packet :
      ((IsScalarTower.toAlgHom ℤ K1 (AlgebraicClosure K1)).compLeft G)
          ((((n : ℕ) : K1)⁻¹) • ρ.ρ.character) =
        ∑ i, (e i : AlgebraicClosure K1) • (ψ i).ρ.character) :
    ∀ i, e i = 1 :=
  by
  -- Route correction: the canonical support owner already packages the orbit-collapse step for
  -- this exact visible packet, so the local theorem is now only a thin adapter.
  simpa using
    visible_scaled_packet_coeff_one_of_irreducible_source_local
      (G := G) (ρ := ρ) (n := n) hcanon hmax
      (ψ := ψ) (d := d) (e := e)
      hd_pos hψ_fd hψ_pairwise hψ_irr hpacket he hscaled_packet

/-- Helper for Exercise 12-12.2-6: after the quotient coefficients collapse, Serre's stabilizer
fixed-field descent should force each visible constituent degree to be a multiple of `n`. -/
private theorem fixedField_block_realization_finrank_multiple_local
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
    (hψ_fd : ∀ i, FiniteDimensional (AlgebraicClosure K1) (ψ i))
    (hψ_pairwise : PairwiseNonisomorphic ψ)
    (hψ_irr : ∀ i, (ψ i).ρ.IsIrreducible)
    (hpacket :
      ((IsScalarTower.toAlgHom ℤ K1 (AlgebraicClosure K1)).compLeft G) ρ.ρ.character =
        ∑ i, (d i : AlgebraicClosure K1) • (ψ i).ρ.character)
    (he : ∀ i, d i = (n : ℕ) * e i)
    (_hscaled_packet :
      ((IsScalarTower.toAlgHom ℤ K1 (AlgebraicClosure K1)).compLeft G)
          ((((n : ℕ) : K1)⁻¹) • ρ.ρ.character) =
        ∑ i, (e i : AlgebraicClosure K1) • (ψ i).ρ.character)
    (hcoeff_one : ∀ i, e i = 1) :
    ∀ i, (n : ℕ) ∣ Module.finrank (AlgebraicClosure K1) (ψ i) := by
  -- Route correction: the canonical support owner already packages the stabilizer fixed-field
  -- descent, so the local theorem again only specializes that reusable bridge.
  simpa using
    visible_packet_constituent_degree_multiple_of_canonical_denominator_local
      (G := G) (ρ := ρ) (n := n) hcanon hmax
      (ψ := ψ) (d := d) (e := e)
      hψ_fd hψ_pairwise hψ_irr hpacket he _hscaled_packet hcoeff_one

/-- Helper for Exercise 12-12.2-6: after the quotient coefficients collapse, Serre's stabilizer
fixed-field descent should force each visible constituent degree to be a multiple of `n`. -/
private theorem stabilizer_fixedField_realization_forces_degree_multiple_local
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
    (hψ_fd : ∀ i, FiniteDimensional (AlgebraicClosure K1) (ψ i))
    (hψ_pairwise : PairwiseNonisomorphic ψ)
    (hψ_irr : ∀ i, (ψ i).ρ.IsIrreducible)
    (hpacket :
      ((IsScalarTower.toAlgHom ℤ K1 (AlgebraicClosure K1)).compLeft G) ρ.ρ.character =
        ∑ i, (d i : AlgebraicClosure K1) • (ψ i).ρ.character)
    (he : ∀ i, d i = (n : ℕ) * e i)
    (hscaled_packet :
      ((IsScalarTower.toAlgHom ℤ K1 (AlgebraicClosure K1)).compLeft G)
          ((((n : ℕ) : K1)⁻¹) • ρ.ρ.character) =
        ∑ i, (e i : AlgebraicClosure K1) • (ψ i).ρ.character)
    (hcoeff_one : ∀ i, e i = 1) :
    ∀ i, (n : ℕ) ∣ Module.finrank (AlgebraicClosure K1) (ψ i) :=
  by
  -- The remaining arithmetic step is now isolated in the theorem-local fixed-field helper above.
  exact
    fixedField_block_realization_finrank_multiple_local
      (G := G) (ρ := ρ) (n := n) hcanon hmax
      (ψ := ψ) (d := d) (e := e)
      hψ_fd hψ_pairwise hψ_irr hpacket he hscaled_packet hcoeff_one

/-- Helper for Exercise 12-12.2-6: the target file now isolates the constituent-degree step to
the stabilizer fixed-field descent frontier above. -/
private theorem visible_packet_constituent_degree_multiple_shadow_local
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
    (hψ_fd : ∀ i, FiniteDimensional (AlgebraicClosure K1) (ψ i))
    (hψ_pairwise : PairwiseNonisomorphic ψ)
    (hψ_irr : ∀ i, (ψ i).ρ.IsIrreducible)
    (hpacket :
      ((IsScalarTower.toAlgHom ℤ K1 (AlgebraicClosure K1)).compLeft G) ρ.ρ.character =
        ∑ i, (d i : AlgebraicClosure K1) • (ψ i).ρ.character)
    (he : ∀ i, d i = (n : ℕ) * e i)
    (hscaled_packet :
      ((IsScalarTower.toAlgHom ℤ K1 (AlgebraicClosure K1)).compLeft G)
          ((((n : ℕ) : K1)⁻¹) • ρ.ρ.character) =
        ∑ i, (e i : AlgebraicClosure K1) • (ψ i).ρ.character)
    (hcoeff_one : ∀ i, e i = 1) :
    ∀ i, (n : ℕ) ∣ Module.finrank (AlgebraicClosure K1) (ψ i) := by
  -- Route correction: the target theorem now points directly at the stabilizer fixed-field
  -- frontier instead of the imported bridge wrapper.
  exact
    stabilizer_fixedField_realization_forces_degree_multiple_local
      (G := G) (ρ := ρ) (n := n) hcanon hmax
      (ψ := ψ) (d := d) (e := e)
      hψ_fd hψ_pairwise hψ_irr hpacket he hscaled_packet hcoeff_one

/-- Helper for Exercise 12-12.2-6: the visible scalar-extension packet for the canonical
denominator reduces the source proof to the single remaining orbit/stabilizer descent step. -/
private theorem canonical_scaled_character_packet_shadow_local
    {K1 : Type v} [Field K1] [CharZero K1]
    (ρ : Rep K1 G)
    [ρ.ρ.IsIrreducible]
    (n : ℕ+)
    (hcanon : ((((n : ℕ) : K1)⁻¹) • ρ.ρ.character) ∈ R̄[K1](G))
    (hmax :
      ∀ d : ℕ+, ((((d : ℕ) : K1)⁻¹) • ρ.ρ.character) ∈ R̄[K1](G) → d ≤ n) :
    ∃ (r : ℕ) (_ : 0 < r) (ψ : Fin r → Rep.{max u v} (AlgebraicClosure K1) G),
      (∀ i, FiniteDimensional (AlgebraicClosure K1) (ψ i)) ∧
      PairwiseNonisomorphic ψ ∧
      (∀ i, (ψ i).ρ.IsIrreducible) ∧
      ((IsScalarTower.toAlgHom ℤ K1 (AlgebraicClosure K1)).compLeft G)
          ((((n : ℕ) : K1)⁻¹) • ρ.ρ.character) =
        ∑ i, (ψ i).ρ.character ∧
      ∀ i, (n : ℕ) ∣ Module.finrank (AlgebraicClosure K1) (ψ i) := by
  classical
  letI : FiniteDimensional K1 ρ :=
    Representation.IsIrreducible.finiteDimensional_of_finite ρ.ρ
  obtain ⟨ι, _, ψ, d, e, hd_pos, hψ_fd, hψ_pairwise, hψ_irr, hpacket, _hcoeff_div, he,
      hscaled_packet⟩ :=
    canonical_scaled_character_visible_packet_frontier_local
      (G := G) (ρ := ρ) (n := n) hcanon hmax
  have hcoeff_one : ∀ i, e i = 1 := by
    -- The orbit-collapse step is now routed through the local theorem-local frontier above.
    exact
      visible_scaled_packet_coeff_one_shadow_local
        (G := G) (ρ := ρ) (n := n) hcanon hmax
        (ψ := ψ) (d := d) (e := e) hd_pos
        hψ_fd hψ_pairwise hψ_irr hpacket he hscaled_packet
  have hψ_degree : ∀ i, (n : ℕ) ∣ Module.finrank (AlgebraicClosure K1) (ψ i) := by
    -- After the coefficient collapse, only the stabilizer fixed-field arithmetic remains.
    exact
      visible_packet_constituent_degree_multiple_shadow_local
        (G := G) (ρ := ρ) (n := n) hcanon hmax
        (ψ := ψ) (d := d) (e := e)
        hψ_fd hψ_pairwise hψ_irr hpacket he hscaled_packet hcoeff_one
  exact
    canonical_scaled_character_packet_of_scaled_visible_packet_coeff_one_shadow_local
      (G := G) (ρ := ρ) (n := n)
      (ψ := ψ) (d := d) (e := e)
      hψ_fd hψ_pairwise hψ_irr hpacket he hcoeff_one hψ_degree

/-- Helper for Exercise 12-12.2-6: evaluating the canonical-multiple honest-fiber identity at `1`
turns the selected isotypic fiber character into the corresponding degree sum. -/
private theorem actual_scalar_extension_isotypic_fiber_degree_sum_eq_local
    {K1 : Type v} [Field K1] [CharZero K1]
    (ρ : Rep K1 G)
    [FiniteDimensional K1 ρ]
    (n : ℕ+)
    {ι : Type*}
    (ψ : ι → Rep.{max u v} (AlgebraicClosure K1) G)
    (a : ℕ)
    (σ : Fin a → Subrepresentation
      (Representation.scalarExtension (k := AlgebraicClosure K1) ρ.ρ))
    (S : ι → Finset (Fin a))
    (hψ_fd : ∀ i, FiniteDimensional (AlgebraicClosure K1) (ψ i))
    (hfiber_char :
      ∀ i,
        Finset.sum
            (S i)
            (fun j ↦ ((σ j).toRepresentation).character) =
          (n : AlgebraicClosure K1) • (ψ i).ρ.character) :
    ∀ i,
      ((Finset.sum (S i)
          (fun j ↦ Module.finrank (AlgebraicClosure K1) ↥((σ j).toSubmodule)) : ℕ) :
          AlgebraicClosure K1) =
        (n : AlgebraicClosure K1) *
          (Module.finrank (AlgebraicClosure K1) (ψ i) : AlgebraicClosure K1) := by
  intro i
  -- Evaluate the honest-fiber character identity at `1` to convert characters into degrees.
  simpa [Representation.char_one, smul_eq_mul] using congrFun (hfiber_char i) 1

/-- Helper for Exercise 12-12.2-6: Proposition `17` over an algebraically closed field sends the
degree of an irreducible constituent to the center index. -/
private theorem finrank_dvd_center_index_over_algClosed_shadow_local
    {L : Type w} [Field L] [CharZero L] [IsAlgClosed L]
    (σ : Rep.{max u w} L G)
    [FiniteDimensional L σ]
    [σ.ρ.IsIrreducible] :
    Module.finrank L σ ∣ (Subgroup.center G).index := by
  -- Proposition `17` remains the only local bridge needed here.
  have hc : 0 < Nat.card (Subgroup.center G) := Nat.card_pos
  refine dvd_of_forall_succ_pow_dvd_center_card_mul_pow hc ?_
  intro m
  obtain ⟨μ, hμ⟩ := center_scalar_action_hom_over_algClosed_local
    (G := G) (ρ := σ.ρ)
  let H : Subgroup (Fin (m + 1) → G) := productOneCenterSubgroup m
  let τ := _root_.Representation.tensorPowerRep_field_local (G := G) σ.ρ (m + 1)
  letI : Representation.IsIrreducible τ :=
    tensor_power_rep_is_irreducible_field_local (G := G) (ρ := σ.ρ) m
  letI : Representation.IsTrivial (τ.comp H.subtype) :=
    _root_.Representation.tensor_power_rep_product_one_center_is_trivial_field_local
      (G := G) (L := L) (ρ := σ.ρ)
      (μ := {
        toFun := fun s ↦ (μ s : L)
        map_one' := by simp
        map_mul' := by
          intro s t
          simp
      }) hμ m
  have hHcenter : H ≤ Subgroup.center (Fin (m + 1) → G) := by
    intro g hg
    rw [Subgroup.mem_center_iff]
    intro h
    ext i
    rcases hg with ⟨z, hz, rfl⟩
    exact Subgroup.mem_center_iff.mp (z i).2 (h i)
  letI : H.Normal := ⟨fun a ha b ↦ by
    have hcomm : b * a = a * b := Subgroup.mem_center_iff.mp (hHcenter ha) b
    simpa [Subgroup.mem_carrier, mul_assoc, hcomm] using ha⟩
  let τquot := τ.ofQuotient H
  letI : Representation.IsIrreducible τquot :=
    ofQuotient_preserves_irreducibility_local (G := Fin (m + 1) → G) τ H
  have hdiv : Module.finrank L (TensorPower L (m + 1) σ) ∣ H.index := by
    -- Apply Corollary 6-6.5-4 to the descended irreducible quotient representation.
    simpa [H, τquot, Subgroup.index_eq_card] using finrank_dvd_card τquot
  -- Rewrite the tensor-power degree and the subgroup index into Serre's arithmetic identity.
  simpa [H, _root_.Representation.tensor_power_finrank_field_local,
    product_one_center_subgroup_index] using hdiv

/-- Helper for Exercise 12-12.2-6: Serre's canonical packet is nonempty, so one visible
constituent already carries the denominator divisibility needed for the final center-index step. -/
private theorem canonical_packet_selected_constituent_degree_multiple_local
    {K1 : Type v} [Field K1] [CharZero K1]
    (ρ : Rep K1 G)
    [ρ.ρ.IsIrreducible]
    (n : ℕ+)
    (hcanon : (((n : ℕ) : K1)⁻¹) • ρ.ρ.character ∈ R̄[K1](G))
    (hmax :
      ∀ d : ℕ+, ((((d : ℕ) : K1)⁻¹) • ρ.ρ.character) ∈ R̄[K1](G) → d ≤ n) :
    ∃ σ : Rep.{max u v} (AlgebraicClosure K1) G,
      FiniteDimensional (AlgebraicClosure K1) σ ∧
      σ.ρ.IsIrreducible ∧
      (n : ℕ) ∣ Module.finrank (AlgebraicClosure K1) σ := by
  obtain ⟨r, hr, ψ, hψ_fd, _hψ_pairwise, hψ_irr, _hscaled_packet, hψ_degree⟩ :=
    canonical_scaled_character_packet_shadow_local
      (G := G) (ρ := ρ) (n := n) hcanon hmax
  let i0 : Fin r := ⟨0, hr⟩
  -- Choose the first constituent of the nonempty canonical packet; its degree already records the
  -- required divisibility information.
  exact ⟨ψ i0, hψ_fd i0, hψ_irr i0, hψ_degree i0⟩

-- Route correction: the complex conclusion now descends the realizing witness directly to the
-- source-side owner `R̄[K](G)`, so the old extension-only center-index bridge is no longer part
-- of the active proof path for this item.

/-- Helper for Exercise 12-12.2-6: Serre's packet argument for the canonical denominator `n`
already yields `n ∣ [G : Z(G)]` before descending back to any smaller admissible denominator. -/
private theorem canonical_denominator_dvd_center_index_local
    {K1 : Type v} [Field K1] [CharZero K1]
    (ρ : Rep K1 G)
    [ρ.ρ.IsIrreducible]
    (n : ℕ+)
    (hcanon : (((n : ℕ) : K1)⁻¹) • ρ.ρ.character ∈ R̄[K1](G))
    (hmax :
      ∀ d : ℕ+, ((((d : ℕ) : K1)⁻¹) • ρ.ρ.character) ∈ R̄[K1](G) → d ≤ n) :
    (n : ℕ) ∣ (Subgroup.center G).index := by
  obtain ⟨σ, hσ_fd, hσ_irr, hσ_degree⟩ :=
    canonical_packet_selected_constituent_degree_multiple_local
      (G := G) (ρ := ρ) (n := n) hcanon hmax
  letI : FiniteDimensional (AlgebraicClosure K1) σ := hσ_fd
  letI : σ.ρ.IsIrreducible := hσ_irr
  -- Choose one visible constituent of the nonempty packet; Serre's degree divisibility and
  -- Proposition `17` then compose to show that `n` divides the center index.
  exact
    dvd_trans hσ_degree
      (finrank_dvd_center_index_over_algClosed_shadow_local
        (G := G) (σ := σ))

/-- Helper for Exercise 12-12.2-6: the public denominator-to-center-index bridge is the
algebraic-closure specialization of the extension theorem above. -/
private theorem scaled_character_denominator_dvd_center_index_via_canonical_local
    {K1 : Type v} [Field K1] [CharZero K1]
    (ρ : Rep K1 G)
    [ρ.ρ.IsIrreducible]
    (m : ℕ+)
    (hscaled : (((m : ℕ) : K1)⁻¹) • ρ.ρ.character ∈ R̄[K1](G)) :
    (m : ℕ) ∣ (Subgroup.center G).index := by
  obtain ⟨n, hcanon, hmax⟩ :=
    exists_schur_denominator_of_irreducible_rep_local
      (K1 := K1) (G := G) ρ
  have hm_dvd_n :
      (m : ℕ) ∣ (n : ℕ) :=
    scaled_character_denominator_dvd_canonical_denominator_local
      (G := G) (ρ := ρ) hcanon hmax hscaled
  have hn_dvd_center :
      (n : ℕ) ∣ (Subgroup.center G).index :=
    canonical_denominator_dvd_center_index_local
      (G := G) (ρ := ρ) (n := n) hcanon hmax
  -- First descend to Serre's canonical denominator, then apply the packet-based center-index
  -- divisibility established for that canonical denominator.
  exact dvd_trans hm_dvd_n hn_dvd_center

/-- Helper for Exercise 12-12.2-6: the public denominator-to-center-index bridge is the
algebraic-closure specialization of the extension theorem above. -/
theorem scaled_character_denominator_dvd_center_index
    (ρ : Rep K G)
    [ρ.ρ.IsIrreducible]
    (m : ℕ+)
    (hscaled : (((m : ℕ) : K)⁻¹) • ρ.ρ.character ∈ R̄[K](G)) :
    (m : ℕ) ∣ (Subgroup.center G).index := by
  -- Reuse the uniform canonical-denominator descent in the ambient field `K`.
  simpa using
    scaled_character_denominator_dvd_center_index_via_canonical_local
      (G := G) (ρ := ρ) (m := m) hscaled

/-- Helper for Exercise 12-12.2-6: the denominator-to-center-index argument is universe-polymorphic
in the coefficient field, so the complex conclusion can apply it to the character field without
forcing `G` into the same universe. -/
private theorem scaled_character_denominator_dvd_center_index_universe_local
    {K1 : Type v} [Field K1] [CharZero K1]
    (ρ : Rep K1 G)
    [ρ.ρ.IsIrreducible]
    (m : ℕ+)
    (hscaled : (((m : ℕ) : K1)⁻¹) • ρ.ρ.character ∈ R̄[K1](G)) :
    (m : ℕ) ∣ (Subgroup.center G).index := by
  -- The same canonical-denominator descent works without tying the field universe to `G`.
  exact
    scaled_character_denominator_dvd_center_index_via_canonical_local
      (G := G) (ρ := ρ) (m := m) hscaled


/-- Helper for Exercise 12-12.2-6: once the denominator divides the center index, multiplying the
scaled character by `[G : Z(G)]` lands in `R_K(G)`. -/
private theorem center_index_smul_scaled_character_eq_integer_smul_local
    (ρ : Rep K G)
    (m : ℕ+)
    (q : ℕ)
    (hq : (Subgroup.center G).index = (m : ℕ) * q) :
    ((Subgroup.center G).index : ℤ) • ((((m : ℕ) : K)⁻¹) • ρ.ρ.character) =
      (q : ℤ) • ρ.ρ.character := by
  have hmK_ne : ((m : ℕ) : K) ≠ 0 := Nat.cast_ne_zero.mpr m.2.ne'
  ext g
  have hqK : (((Subgroup.center G).index : ℤ) : K) = ((m : ℕ) : K) * (q : K) := by
    exact_mod_cast hq
  -- Rewrite the center index through the divisibility witness and cancel the denominator.
  simp only [Pi.smul_apply, smul_eq_mul, zsmul_eq_mul]
  rw [hqK]
  field_simp [hmK_ne]
  simp [mul_comm]

/-- Helper for Exercise 12-12.2-6: once the denominator divides the center index, multiplying the
scaled character by `[G : Z(G)]` lands in `R_K(G)`. -/
private theorem center_index_smul_scaled_character_mem_characterRing
    (ρ : Rep K G) [ρ.ρ.IsIrreducible]
    (m : ℕ+)
    (hscaled : (((m : ℕ) : K)⁻¹) • ρ.ρ.character ∈ R̄[K](G)) :
    ((Subgroup.center G).index : ℤ) • ((((m : ℕ) : K)⁻¹) • ρ.ρ.character) ∈ R[K](G) := by
  obtain ⟨q, hq⟩ :=
    scaled_character_denominator_dvd_center_index (K := K) (G := G) (ρ := ρ) (m := m) hscaled
  letI : FiniteDimensional K ρ := Representation.IsIrreducible.finiteDimensional_of_finite ρ.ρ
  have hchar_mem : ρ.ρ.character ∈ (R[K](G)).toSubmodule := by
    simpa using
      rep_character_mem_characterRingOverField_universe_local
        (K' := K) (H := G) (ρ := ρ.ρ)
  change ((Subgroup.center G).index : ℤ) • ((((m : ℕ) : K)⁻¹) • ρ.ρ.character) ∈
    (R[K](G)).toSubmodule
  rw [center_index_smul_scaled_character_eq_integer_smul_local
    (K := K) (G := G) (ρ := ρ) (m := m) (q := q) hq]
  exact Submodule.smul_mem _ _ hchar_mem

/-- Helper for Exercise 12-12.2-6: multiplying a scaled basis vector from Proposition
`12-12.2-1` by the center index lands in `R_K(G)`. -/
private theorem center_index_smul_scaled_basis_mem_characterRing
    {ι : Type*} [Finite ι]
    (π : ι → FDRep K G)
    (hπ_pairwise : PairwiseNonisomorphic π)
    (hπ_complete : IsCompleteIrreducibleFamily π)
    (m : ι → ℕ+)
    (hdenom : ∀ i, FDRep.IsSchurDenominator (π i) (m i))
    (i : ι) :
    ((Subgroup.center G).index : ℤ) •
        (((scaled_irreducible_characters_basis_of_complete_family
            π hπ_pairwise hπ_complete m hdenom i : R̄[K](G)) : G → K)) ∈
      R[K](G) := by
  letI : Fintype ι := Fintype.ofFinite ι
  letI : Simple (π i) := hπ_complete.isSimple i
  letI : (Rep.of (π i).ρ).ρ.IsIrreducible := by
    simpa using (FDRep.isIrreducible_of_simple (π i))
  have hbasis :
      (((scaled_irreducible_characters_basis_of_complete_family
          π hπ_pairwise hπ_complete m hdenom i : R̄[K](G)) : G → K)) =
        FDRep.schurScaledCharacter (π i) (m i) := by
    exact
      congrArg (fun z : R̄[K](G) ↦ (z : G → K))
        (scaled_irreducible_characters_basis_of_complete_family_apply
          π hπ_pairwise hπ_complete m hdenom i)
  simpa [hbasis, FDRep.schurScaledCharacter] using
    center_index_smul_scaled_character_mem_characterRing
      (K := K) (G := G) (ρ := Rep.of (π i).ρ) (m := m i) (by simpa using (hdenom i).1)

omit [CharZero K] [Finite G] in
/-- Helper for Exercise 12-12.2-6: basis coefficients commute with the center-index scalar when
clearing denominators termwise. -/
private theorem coeff_smul_center_index_comm_local
    (a : ℤ)
    (χ : G → K) :
    a • (((Subgroup.center G).index : ℤ) • χ) =
      ((Subgroup.center G).index : ℤ) • (a • χ) := by
  -- Both sides are the same pointwise product in the commutative coefficient field.
  ext g
  simp [zsmul_eq_mul, mul_assoc, mul_left_comm, mul_comm]

omit [CharZero K] [Finite G] in
/-- Helper for Exercise 12-12.2-6: the fixed center-index scalar distributes across the finite
basis expansion used to clear denominators termwise. -/
private theorem center_index_smul_sum_local
    {ι : Type*} [Fintype ι]
    (c : ι → ℤ)
    (b : ι → G → K) :
    ((Subgroup.center G).index : ℤ) • (∑ i, c i • b i) =
      ∑ i, ((Subgroup.center G).index : ℤ) • (c i • b i) := by
  -- Evaluate pointwise and pull the fixed scalar through the finite sum.
  ext g
  simp [zsmul_eq_mul, Finset.mul_sum, mul_assoc, mul_comm]

/-- Consequence of Exercise 12-12.2-6: multiplying any element of `\overline{R}_K(G)` by
`a = [G : Z(G)]` places it in `R_K(G)`. -/
theorem center_index_smul_mem_characterRingOverField
    (χ : R̄[K](G)) :
    ((Subgroup.center G).index : ℤ) • (χ : G → K) ∈ R[K](G) := by
  classical
  have hcard_ne : (Nat.card G : K) ≠ 0 := by
    exact Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  letI : NeZero (Nat.card G : K) := ⟨hcard_ne⟩
  obtain ⟨ι, hι, π, hπ_pairwise, hπ_complete⟩ :=
    _root_.Representation.exists_complete_pairwise_nonisomorphic_simple_family_local
      (K := K) (G := G)
  letI : Fintype ι := hι
  choose m hdenom using
    fun i ↦ exists_schur_denominator_of_simple_local (K := K) (G := G) (π i)
  let b :=
    scaled_irreducible_characters_basis_of_complete_family π hπ_pairwise hπ_complete m hdenom
  let c := b.repr χ
  have hx :
      ∑ i, c i • ((b i : R̄[K](G)) : G → K) = (χ : G → K) := by
    -- Expand `χ` in the scaled-character basis before clearing denominators termwise.
    simpa [b, c] using
      congrArg (fun z : R̄[K](G) ↦ (z : G → K)) (b.sum_repr χ)
  rw [← hx]
  change
      ((Subgroup.center G).index : ℤ) •
          (∑ i, c i • ((b i : R̄[K](G)) : G → K)) ∈
        (R[K](G)).toSubmodule
  -- Distribute the fixed center-index scalar across the basis expansion before summing in
  -- `R[K](G)`.
  rw [center_index_smul_sum_local
    (K := K) (G := G) (c := fun i ↦ c i) (b := fun i ↦ ((b i : R̄[K](G)) : G → K))]
  refine Submodule.sum_mem _ ?_
  intro i _
  have hbasis_mem :
      ((Subgroup.center G).index : ℤ) • ((b i : R̄[K](G)) : G → K) ∈ R[K](G) :=
    center_index_smul_scaled_basis_mem_characterRing
      (K := K) (G := G) (π := π) hπ_pairwise hπ_complete m hdenom i
  have hsmul_mem :
      (c i) • (((Subgroup.center G).index : ℤ) • ((b i : R̄[K](G)) : G → K)) ∈
        (R[K](G)).toSubmodule := by
    exact Submodule.smul_mem (R[K](G)).toSubmodule (c i) (by simpa using hbasis_mem)
  -- Move the basis coefficient across the center-index action before summing in `R[K](G)`.
  exact
    (coeff_smul_center_index_comm_local
      (K := K) (G := G) (a := c i) (χ := ((b i : R̄[K](G)) : G → K))).symm ▸ hsmul_mem

end FieldPart

section ComplexConclusion

variable {G : Type u} [Group G] [Finite G]

/-- Helper for Exercise 12-12.2-6: precomposing a virtual character with a multiplicative
equivalence preserves character-ring membership. This earlier local owner lets the Shrink bridge
reuse the transport before the later identical general helper is declared. -/
private theorem mem_characterRingOverField_of_precomp_mulEquiv_shrink_local
    {K' : Type*} [Field K']
    {G₀ : Type*} [Group G₀] [Finite G₀]
    {H : Type*} [Group H] [Finite H]
    (e : H ≃* G₀) {χ : G₀ → K'} (hχ : χ ∈ R[K'](G₀)) :
    (fun h : H ↦ χ (e h)) ∈ R[K'](H) := by
  -- Transport each honest character generator through the multiplicative equivalence `e`.
  refine Algebra.adjoin_induction ?_ ?_ ?_ ?_ hχ
  · intro ψ hψ
    rcases hψ with ⟨ρ, hρfd, -, rfl⟩
    letI : FiniteDimensional K' ρ := hρfd
    let τρ : Representation K' H ρ := ρ.ρ.comp e.toMonoidHom
    have hτρ :
        τρ.character = fun h : H ↦ ρ.ρ.character (e h) := by
      -- Character transport across precomposition is pointwise definitional.
      ext h
      rfl
    exact hτρ ▸
      rep_character_mem_characterRingOverField_universe_local
        (K' := K') (H := H) (ρ := τρ)
  · intro n
    exact (R[K'](H)).algebraMap_mem n
  · intro f g _ _ hf hg
    simpa using (R[K'](H)).add_mem hf hg
  · intro f g _ _ hf hg
    simpa using (R[K'](H)).mul_mem hf hg

/-- Helper for Exercise 12-12.2-6: the one-dimensional representation attached to a unit-valued
character sends the identity to the identity endomorphism. -/
private theorem oneDimensionalRepresentation_map_one_shrink_local
    {K : Type*} [Field K]
    {H : Type*} [Group H]
    (β : H →* Kˣ) :
    LinearMap.lsmul K K ((β 1 : Kˣ) : K) = 1 := by
  -- At the identity, the action is scalar multiplication by `1`.
  ext
  simp [LinearMap.lsmul_apply]

/-- Helper for Exercise 12-12.2-6: the one-dimensional representation attached to a unit-valued
character is multiplicative. -/
private theorem oneDimensionalRepresentation_map_mul_shrink_local
    {K : Type*} [Field K]
    {H : Type*} [Group H]
    (β : H →* Kˣ) (x y : H) :
    LinearMap.lsmul K K ((β (x * y) : Kˣ) : K) =
      LinearMap.lsmul K K ((β x : Kˣ) : K) *
        LinearMap.lsmul K K ((β y : Kˣ) : K) := by
  -- Composition of scalar multiplications multiplies the scalars.
  ext
  simp [LinearMap.lsmul_apply, mul_comm]

/-- Helper for Exercise 12-12.2-6: a unit-valued character defines a one-dimensional
representation over the source field. -/
private def oneDimensionalRepresentation_shrink_local
    {K : Type*} [Field K]
    {H : Type*} [Group H]
    (β : H →* Kˣ) : Representation K H K where
  toFun h := LinearMap.lsmul K K ((β h : Kˣ) : K)
  map_one' := oneDimensionalRepresentation_map_one_shrink_local (K := K) β
  map_mul' x y := oneDimensionalRepresentation_map_mul_shrink_local (K := K) β x y

/-- Helper for Exercise 12-12.2-6: the character of the attached one-dimensional representation
recovers the original scalar-valued homomorphism. -/
private theorem oneDimensionalRepresentation_character_apply_shrink_local
    {K : Type*} [Field K]
    {H : Type*} [Group H]
    (β : H →* Kˣ) (h : H) :
    (oneDimensionalRepresentation_shrink_local (K := K) β).character h = ((β h : Kˣ) : K) := by
  -- The trace of scalar multiplication on a one-dimensional space is that scalar.
  rw [Representation.character]
  let b := Module.Free.chooseBasis K K
  rw [LinearMap.trace_eq_matrix_trace K b]
  have hmat :
      LinearMap.toMatrix b b (oneDimensionalRepresentation_shrink_local (K := K) β h) =
        Matrix.diagonal fun _ ↦ ((β h : Kˣ) : K) := by
    convert (Algebra.toMatrix_lsmul (b := b) (((β h : Kˣ) : K))) using 1
  rw [hmat]
  have hcard : Fintype.card (Module.Free.ChooseBasisIndex K K) = 1 := by
    rw [← Module.finrank_eq_card_chooseBasisIndex K K]
    rw [Module.finrank_self]
  simp [Matrix.trace, hcard]

/-- Helper for Exercise 12-12.2-6: values of a linear character have order dividing the group
exponent, so they land in the corresponding roots-of-unity subgroup. -/
private theorem linearCharacter_mem_rootsOfUnity_shrink_local
    {G' : Type*} [Group G'] [Finite G']
    (H : Subgroup G') (α : H →* ℂˣ) (h : H) :
    α h ∈ rootsOfUnity (Monoid.exponent G') ℂ := by
  let m := Monoid.exponent G'
  have hh : h ^ m = 1 := by
    apply H.subtype_injective
    simpa [m] using Monoid.pow_exponent_eq_one (h : G')
  rw [mem_rootsOfUnity]
  simpa [← map_pow] using congrArg α hh

/-- Helper for Exercise 12-12.2-6: if the source field contains the required roots of unity, then
every induced linear character already lies in the coefficient-extension character ring. -/
private theorem
    induced_linear_character_mem_extension_of_hasEnoughRoots_shrink_local
    {K : Type*} [Field K] [CharZero K] [Algebra K ℂ]
    {G' : Type*} [Group G'] [Finite G']
    [HasEnoughRootsOfUnity K (Monoid.exponent G')]
    (H : Subgroup G') (α : H →* ℂˣ) :
    Ind[H](α.toRepresentation.character) ∈ characterRingOverFieldInExtension K ℂ G' := by
  letI : Fintype H := Fintype.ofFinite H
  let m := Monoid.exponent G'
  letI : NeZero m := Monoid.neZero_exponent_of_finite
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot K m
  have hprim : (primitiveRoots m K).Nonempty := by
    refine ⟨ζ, ?_⟩
    rw [mem_primitiveRoots (NeZero.pos m)]
    exact hζ
  let e : rootsOfUnity m K ≃* rootsOfUnity m ℂ :=
    rootsOfUnityEquivOfPrimitiveRoots (f := algebraMap K ℂ) (algebraMap K ℂ).injective hprim
  let αRoots : H →* rootsOfUnity m ℂ :=
    MonoidHom.codRestrict α (rootsOfUnity m ℂ)
      (fun h ↦ linearCharacter_mem_rootsOfUnity_shrink_local H α h)
  let βRoots : H →* rootsOfUnity m K := e.symm.toMonoidHom.comp αRoots
  let β : H →* Kˣ := (rootsOfUnity m K).subtype.comp βRoots
  let χK : R[K](H) :=
    ⟨(oneDimensionalRepresentation_shrink_local (K := K) β).character,
      rep_character_mem_characterRingOverField_universe_local
        (K' := K) (H := H) (ρ := oneDimensionalRepresentation_shrink_local (K := K) β)⟩
  refine Subalgebra.mem_map.mpr ?_
  refine ⟨Ind[H]((χK : H → K)), Subgroup.inducedClassFunction_mem_characterRingOverField H χK, ?_⟩
  -- Compare the induced `K`-character with the original complex induced character termwise.
  ext g
  simp [Subgroup.inducedClassFunction]
  refine Finset.sum_congr rfl ?_
  intro s hs
  by_cases hsg : s⁻¹ * g * s ∈ H
  · simp [hsg, χK, oneDimensionalRepresentation_character_apply_shrink_local]
    simpa [β, βRoots, αRoots, e, hsg, MonoidHom.toRepresentation_character_apply] using
      rootsOfUnityEquivOfPrimitiveRoots_symm_apply
        (f := algebraMap K ℂ) (n := m) (algebraMap K ℂ).injective hprim
        (αRoots ⟨s⁻¹ * g * s, hsg⟩)
  · simp [hsg]

/-- Helper for Exercise 12-12.2-6: enough roots of unity identify the coefficient-extension image
of `R_K(G')` with the ordinary complex character ring. -/
private theorem
    characterRing_le_characterRingOverFieldInExtension_of_hasEnoughRootsOfUnity_shrink_local
    {K : Type*} [Field K] [CharZero K] [Algebra K ℂ] [IsAlgClosed K]
    {G' : Type u} [Group G'] [Finite G']
    [HasEnoughRootsOfUnity K (Monoid.exponent G')] :
    R[ℂ](G') ≤ characterRingOverFieldInExtension K ℂ G' := by
  intro χ hχ
  let Gs := Shrink.{0} G'
  let e : Gs ≃* G' := Shrink.mulEquiv
  let χH : Gs → ℂ := fun h ↦ χ (e h)
  have hχH : χH ∈ R[ℂ](Gs) := by
    -- Shrink to the small-universe owner where Brauer's monomial span theorem is available.
    simpa [Gs, e, χH] using
      mem_characterRingOverField_of_precomp_mulEquiv_shrink_local
        (K' := ℂ) (G₀ := G') (H := Gs) e hχ
  let χHR : R[ℂ](Gs) := ⟨χH, hχH⟩
  have hmono : χHR ∈ monomialCharacterSpan Gs := by
    -- The Chapter 10 monomial-span theorem applies after shrinking the carrier universe.
    exact Representation.character_mem_monomialCharacterSpan χHR
  have hχ_ext :
      (χHR : Gs → ℂ) ∈ (characterRingOverFieldInExtension K ℂ Gs).toSubmodule := by
    -- Check the target on monomial generators and then use the target submodule's closure.
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hmono
    · intro η hη
      rcases hη with ⟨L, α, hηeq⟩
      simpa [← hηeq] using
        induced_linear_character_mem_extension_of_hasEnoughRoots_shrink_local
          (K := K) (G' := Gs) L α
    · simpa using (characterRingOverFieldInExtension K ℂ Gs).toSubmodule.zero_mem
    · intro η ξ _ _ hη hξ
      simpa using (characterRingOverFieldInExtension K ℂ Gs).toSubmodule.add_mem hη hξ
    · intro n η _ hη
      simpa using (characterRingOverFieldInExtension K ℂ Gs).toSubmodule.smul_mem n hη
  have hχH_ext : χH ∈ characterRingOverFieldInExtension K ℂ Gs := by
    simpa [χHR] using hχ_ext
  rcases Subalgebra.mem_map.mp hχH_ext with ⟨χK, hχK, hχK_map⟩
  let χKG : G' → K := fun g ↦ χK (e.symm g)
  have hχKG : χKG ∈ R[K](G') := by
    -- Transport the realizing `K`-character back along the inverse shrink equivalence.
    simpa [Gs, e, χKG] using
      mem_characterRingOverField_of_precomp_mulEquiv_shrink_local
        (K' := K) (G₀ := Gs) (H := G') e.symm hχK
  refine Subalgebra.mem_map.mpr ?_
  refine ⟨χKG, hχKG, ?_⟩
  ext g
  simpa [Gs, e, χKG, χH] using congrFun hχK_map (e.symm g)

/-- Helper for Exercise 12-12.2-6: enough roots of unity identify the coefficient-extension image
of `R_K(G')` with the ordinary complex character ring. -/
private theorem characterRing_extension_eq_characterRing_of_hasEnoughRoots_shrink_local
    {K : Type*} [Field K] [CharZero K] [Algebra K ℂ] [IsAlgClosed K]
    {G' : Type u} [Group G'] [Finite G']
    [HasEnoughRootsOfUnity K (Monoid.exponent G')] :
    characterRingOverFieldInExtension K ℂ G' = R[ℂ](G') := by
  apply le_antisymm
  · intro χ hχ
    rcases Subalgebra.mem_map.mp hχ with ⟨χK, hχK, rfl⟩
    -- Coefficientwise extension of a `K`-virtual character is always an ordinary complex one.
    simpa using
      map_mem_characterRingOverField_local
        (G := G') (f := (IsScalarTower.toAlgHom ℤ K ℂ)) χK hχK
  · intro χ hχ
    -- The reverse inclusion is the monomial-generator reduction proved just above.
    exact
      characterRing_le_characterRingOverFieldInExtension_of_hasEnoughRootsOfUnity_shrink_local
        (K := K) (G' := G') hχ

/-- Helper for Exercise 12-12.2-6: in the only case needed later, an algebraically closed source
field has enough roots of unity to realize every complex virtual character over `R_K(G)`. -/
private theorem characterRingOverFieldInExtension_eq_characterRing_of_algClosed_toComplex_local
    {K : Type*} [Field K] [CharZero K] [Algebra K ℂ] [IsAlgClosed K] :
    characterRingOverFieldInExtension K ℂ G = R[ℂ](G) := by
  simpa using
    (characterRing_extension_eq_characterRing_of_hasEnoughRoots_shrink_local
      (K := K) (G' := G))

/-- Helper for Exercise 12-12.2-6: dividing a realizing equality for `m • χ_ρ` yields the
mapped scaled realizing character itself. -/
private theorem scaled_realizing_character_maps_to_complex_local
    (ρ : Rep.{v} ℂ G)
    [ρ.ρ.IsIrreducible]
    (τ : Rep (characterField ρ.ρ.character) G)
    [FiniteDimensional (characterField ρ.ρ.character) τ]
    (m : ℕ+)
    (hτchar :
      (fun g ↦ algebraMap (characterField ρ.ρ.character) ℂ (τ.ρ.character g)) =
        (((m : ℕ) : ℂ) • ρ.ρ.character)) :
    let K := characterField ρ.ρ.character
    let χ : G → K := (((m : ℕ) : K)⁻¹) • τ.ρ.character
    (fun g ↦ algebraMap K ℂ (χ g)) = ρ.ρ.character := by
  let _ : Finite G := inferInstance
  let K := characterField ρ.ρ.character
  let χ : G → K := (((m : ℕ) : K)⁻¹) • τ.ρ.character
  -- Divide the realizing equality by `m` after mapping the scaled character into `ℂ`.
  ext g
  have hm_ne : (((m : ℕ) : ℂ)) ≠ 0 := Nat.cast_ne_zero.mpr m.2.ne'
  have hpoint := congrFun hτchar g
  calc
    algebraMap K ℂ (χ g) = (((m : ℕ) : ℂ)⁻¹) * algebraMap K ℂ (τ.ρ.character g) := by
      simp [χ, map_mul]
    _ = (((m : ℕ) : ℂ)⁻¹) * (((m : ℕ) : ℂ) * ρ.ρ.character g) := by
      rw [hpoint]
      simp [smul_eq_mul]
    _ = ρ.ρ.character g := by
      field_simp [hm_ne]

/-- Helper for Exercise 12-12.2-6: dividing a realizing equality for `m • χ_ρ` yields the
canonical source-side overline witness for the realizing model. -/
private theorem schur_realization_scaled_character_mem_overline_local
    (ρ : Rep.{v} ℂ G)
    [ρ.ρ.IsIrreducible]
    (τ : Rep (characterField ρ.ρ.character) G)
    [FiniteDimensional (characterField ρ.ρ.character) τ]
    (m : ℕ+)
    (hτchar :
      (fun g ↦ algebraMap (characterField ρ.ρ.character) ℂ (τ.ρ.character g)) =
        (((m : ℕ) : ℂ) • ρ.ρ.character)) :
    ((((m : ℕ) : characterField ρ.ρ.character)⁻¹) • τ.ρ.character) ∈
      R̄[characterField ρ.ρ.character](G) := by
  let K := characterField ρ.ρ.character
  let χ : G → K := (((m : ℕ) : K)⁻¹) • τ.ρ.character
  let ι : AlgebraicClosure K →ₐ[K] ℂ := IsAlgClosed.lift (R := K)
  letI : Algebra (AlgebraicClosure K) ℂ := ι.toAlgebra
  let ιZ : AlgebraicClosure K →ₐ[ℤ] ℂ := ι.restrictScalars ℤ
  letI : FiniteDimensional ℂ ρ := Representation.IsIrreducible.finiteDimensional_of_finite ρ.ρ
  have hρ_mem : ρ.ρ.character ∈ R[ℂ](G) := by
    simpa using
      rep_character_mem_characterRingOverField_universe_local
        (K' := ℂ) (H := G) (ρ := ρ.ρ)
  have hχ_complex :
      (ιZ.compLeft G) (((IsScalarTower.toAlgHom ℤ K (AlgebraicClosure K)).compLeft G) χ) =
        ρ.ρ.character := by
    -- First map the scaled realizing character into `ℂ`; this is exactly the previous scalar
    -- division identity, now rewritten through the algebraic closure.
    ext g
    change algebraMap (AlgebraicClosure K) ℂ (algebraMap K (AlgebraicClosure K) (χ g)) =
      ρ.ρ.character g
    calc
      algebraMap (AlgebraicClosure K) ℂ (algebraMap K (AlgebraicClosure K) (χ g))
          = algebraMap K ℂ (χ g) := by
              exact AlgHom.commutes ι (χ g)
      _ = ρ.ρ.character g := by
            simpa [K, χ] using
              congrFun
                (scaled_realizing_character_maps_to_complex_local
                  (ρ := ρ) (τ := τ) (m := m) hτchar) g
  have hχ_in_extension :
      (ιZ.compLeft G) (((IsScalarTower.toAlgHom ℤ K (AlgebraicClosure K)).compLeft G) χ) ∈
        characterRingOverFieldInExtension (AlgebraicClosure K) ℂ G := by
    -- Over the algebraic closure, the new Shrink-based equality bridge turns the mapped scaled
    -- character into an honest complex virtual character.
    rw [characterRingOverFieldInExtension_eq_characterRing_of_algClosed_toComplex_local
      (G := G) (K := AlgebraicClosure K)]
    exact hχ_complex.symm ▸ hρ_mem
  rcases Subalgebra.mem_map.mp hχ_in_extension with ⟨ψ, hψ, hψmap⟩
  have hψ_eq :
      ψ = ((IsScalarTower.toAlgHom ℤ K (AlgebraicClosure K)).compLeft G) χ := by
    -- The algebraic-closure witness is determined by its image in `ℂ`.
    ext g
    apply ι.injective
    exact congrFun hψmap g
  -- Repackage the algebraic-closure witness as the source-facing overline-character condition.
  exact (mem_overlineCharacterRingInExtension_iff K (AlgebraicClosure K) χ).2 <| by
    simpa [K, χ, hψ_eq] using hψ

/-- Exercise 12-12.2-6 (1): the Schur index of an irreducible complex representation divides the
index of the center `a = [G : Z(G)]`. -/
theorem schurIndex_dvd_center_index
    (ρ : Rep.{v} ℂ G)
    [ρ.ρ.IsIrreducible]
    (m : ℕ+)
    (hm : HasSchurIndex ρ.ρ.character m) :
    (m : ℕ) ∣ (Subgroup.center G).index := by
  let K := characterField ρ.ρ.character
  rcases (hasSchurIndex_iff_packaged_realization_local (χ := ρ.ρ.character) (m := m)).1 hm with
    ⟨⟨τ, hτfd, hτchar⟩, hmin⟩
  let _ : FiniteDimensional K τ := hτfd
  have hτirr :
      τ.ρ.IsIrreducible :=
    minimal_realization_is_irreducible_local
      (ρ := ρ) (τ := τ) (m := m) hτchar hmin
  letI : τ.ρ.IsIrreducible := hτirr
  have hscaled :
      ((((m : ℕ) : K)⁻¹) • τ.ρ.character) ∈ R̄[K](G) :=
    schur_realization_scaled_character_mem_overline_local
      (ρ := ρ) (τ := τ) (m := m) hτchar
  -- The complex Schur-index statement is now reduced to the field-side denominator theorem.
  exact
    scaled_character_denominator_dvd_center_index_universe_local
      (G := G) (ρ := τ) (m := m) hscaled

end ComplexConclusion

end Representation
