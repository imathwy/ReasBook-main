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
import LinearRepresentations_Serre_1977.Chap12.Exercise_12_12_2_6.PacketCenterDescentCore
import LinearRepresentations_Serre_1977.Chap12.Exercise_12_12_2_6.ScalarExtensionBlockProjectors
import LinearRepresentations_Serre_1977.Chap12.Exercise_12_12_2_6.ScalarExtensionConstituents
import LinearRepresentations_Serre_1977.Chap12.Exercise_12_12_2_6.ScalarExtensionPackets
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

local instance instFintypeGExercise_12_12_2_6_packet_center : Fintype G := Fintype.ofFinite G

/-- Helper for Exercise 12-12.2-6: once LinearRepresentations_Serre_1977's visible algebraic-closure packet already has the
canonical common coefficient `n`, the target `χ_i / m_i = ∑ ψ_{i,σ}` statement is just the
rescaling and `Fin`-reindexing of that packet. -/
theorem canonical_scaled_character_packet_of_public_common_coeff_local
    {K' : Type v} [Field K'] [CharZero K']
    (ρ : Rep K' G)
    [ρ.ρ.IsIrreducible]
    (n : ℕ+)
    {ι : Type*} [Fintype ι]
    (ψ : ι → Rep.{max u v} (AlgebraicClosure K') G)
    (hψ_fd : ∀ i, FiniteDimensional (AlgebraicClosure K') (ψ i))
    (hψ_pairwise : PairwiseNonisomorphic ψ)
    (hψ_irr : ∀ i, (ψ i).ρ.IsIrreducible)
    (hpacket :
      ((IsScalarTower.toAlgHom ℤ K' (AlgebraicClosure K')).compLeft G) ρ.ρ.character =
        ∑ i, (n : AlgebraicClosure K') • (ψ i).ρ.character)
    (hψ_degree : ∀ i, (n : ℕ) ∣ Module.finrank (AlgebraicClosure K') (ψ i)) :
    ∃ (r : ℕ) (_ : 0 < r) (ψ' : Fin r → Rep.{max u v} (AlgebraicClosure K') G),
      (∀ i, FiniteDimensional (AlgebraicClosure K') (ψ' i)) ∧
      PairwiseNonisomorphic ψ' ∧
      (∀ i, (ψ' i).ρ.IsIrreducible) ∧
      ((IsScalarTower.toAlgHom ℤ K' (AlgebraicClosure K')).compLeft G)
          ((((n : ℕ) : K')⁻¹) • ρ.ρ.character) =
        ∑ i, (ψ' i).ρ.character ∧
      ∀ i, (n : ℕ) ∣ Module.finrank (AlgebraicClosure K') (ψ' i) := by
  classical
  letI : FiniteDimensional K' ρ :=
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
        algebraMap K' (AlgebraicClosure K') (Module.finrank K' ρ) ≠ 0 := by
      exact Nat.cast_ne_zero.mpr ((Module.finrank_pos_iff.mpr hρ_nontriv).ne')
    have hzero :
        algebraMap K' (AlgebraicClosure K') (Module.finrank K' ρ) = 0 := by
      simpa [Representation.char_one] using congrFun hpacket 1
    exact hdim_ne hzero
  let r : ℕ := Fintype.card ι
  have hr : 0 < r := by
    simpa [r] using Fintype.card_pos_iff.mpr hι_nonempty
  let e : Fin r ≃ ι := (Fintype.equivFin ι).symm
  let ψ' : Fin r → Rep.{max u v} (AlgebraicClosure K') G := fun i ↦ ψ (e i)
  have hψ'_fd : ∀ i, FiniteDimensional (AlgebraicClosure K') (ψ' i) := by
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
      ((IsScalarTower.toAlgHom ℤ K' (AlgebraicClosure K')).compLeft G)
          ((((n : ℕ) : K')⁻¹) • ρ.ρ.character) =
        ∑ i, (ψ i).ρ.character := by
    -- Divide the common coefficient `n` out of the visible packet term by term.
    ext g
    have hn_ne : ((n : ℕ) : AlgebraicClosure K') ≠ 0 := Nat.cast_ne_zero.mpr n.2.ne'
    calc
      ((IsScalarTower.toAlgHom ℤ K' (AlgebraicClosure K')).compLeft G)
          ((((n : ℕ) : K')⁻¹) • ρ.ρ.character) g
          = (((n : ℕ) : AlgebraicClosure K')⁻¹) *
              (((IsScalarTower.toAlgHom ℤ K' (AlgebraicClosure K')).compLeft G)
                ρ.ρ.character g) := by
                  simp [smul_eq_mul, map_mul, mul_assoc]
      _ = (((n : ℕ) : AlgebraicClosure K')⁻¹) *
            ((∑ i, (n : AlgebraicClosure K') • (ψ i).ρ.character) g) := by
              rw [hpacket]
      _ = (∑ i, (ψ i).ρ.character) g := by
            simp [smul_eq_mul, Finset.mul_sum, hn_ne, mul_assoc, mul_left_comm, mul_comm]
  have hscaled_packet' :
      ((IsScalarTower.toAlgHom ℤ K' (AlgebraicClosure K')).compLeft G)
          ((((n : ℕ) : K')⁻¹) • ρ.ρ.character) =
        ∑ i, (ψ' i).ρ.character := by
    -- Reindex the finite packet along the explicit `Fin r` owner used by the main theorem.
    calc
      ((IsScalarTower.toAlgHom ℤ K' (AlgebraicClosure K')).compLeft G)
          ((((n : ℕ) : K')⁻¹) • ρ.ρ.character)
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

/-- Helper for Exercise 12-12.2-6: dividing the visible packet coefficients by the canonical
denominator rewrites the mapped scaled character as a weighted sum of the same packet
constituents. -/
theorem scaled_visible_packet_of_canonical_denominator_local
    {K' : Type v} [Field K'] [CharZero K']
    (ρ : Rep K' G)
    [FiniteDimensional K' ρ]
    (n : ℕ+)
    {ι : Type*} [Fintype ι]
    (ψ : ι → Rep.{max u v} (AlgebraicClosure K') G)
    (d : ι → ℕ)
    (hpacket :
      ((IsScalarTower.toAlgHom ℤ K' (AlgebraicClosure K')).compLeft G) ρ.ρ.character =
        ∑ i, (d i : AlgebraicClosure K') • (ψ i).ρ.character)
    (hcoeff_div : ∀ i, (n : ℕ) ∣ d i) :
    ∃ e : ι → ℕ,
      (∀ i, d i = (n : ℕ) * e i) ∧
      ((IsScalarTower.toAlgHom ℤ K' (AlgebraicClosure K')).compLeft G)
          ((((n : ℕ) : K')⁻¹) • ρ.ρ.character) =
        ∑ i, (e i : AlgebraicClosure K') • (ψ i).ρ.character := by
  classical
  choose e he using hcoeff_div
  refine ⟨e, ?_, ?_⟩
  · -- Record the exact quotient coefficients `d i = n * e i` for the later orbit-collapse step.
    intro i
    exact he i
  · -- Rewrite the mapped scaled character by cancelling the visible common factor `n` termwise.
    ext g
    have hn_ne : ((n : ℕ) : AlgebraicClosure K') ≠ 0 := Nat.cast_ne_zero.mpr n.2.ne'
    calc
      ((IsScalarTower.toAlgHom ℤ K' (AlgebraicClosure K')).compLeft G)
          ((((n : ℕ) : K')⁻¹) • ρ.ρ.character) g
          = (((n : ℕ) : AlgebraicClosure K')⁻¹) *
              (((IsScalarTower.toAlgHom ℤ K' (AlgebraicClosure K')).compLeft G)
                ρ.ρ.character g) := by
                  simp [smul_eq_mul, map_mul, mul_assoc]
      _ = (((n : ℕ) : AlgebraicClosure K')⁻¹) *
            ((∑ i, (d i : AlgebraicClosure K') • (ψ i).ρ.character) g) := by
              rw [hpacket]
      _ = (∑ i, (e i : AlgebraicClosure K') • (ψ i).ρ.character) g := by
            simp [smul_eq_mul, Finset.mul_sum, he, hn_ne, mul_assoc, mul_left_comm, mul_comm]

/-- Helper for Exercise 12-12.2-6: the canonical source denominator yields LinearRepresentations_Serre_1977's packet
`χ_i / m_i = ∑_σ ψ_{i,σ}` after scalar extension to the algebraic closure. -/
theorem canonical_scaled_character_packet_of_scaled_visible_packet_coeff_one_local
    {K' : Type v} [Field K'] [CharZero K']
    (ρ : Rep K' G)
    [ρ.ρ.IsIrreducible]
    (n : ℕ+)
    {ι : Type*} [Fintype ι]
    (ψ : ι → Rep.{max u v} (AlgebraicClosure K') G)
    (d e : ι → ℕ)
    (hψ_fd : ∀ i, FiniteDimensional (AlgebraicClosure K') (ψ i))
    (hψ_pairwise : PairwiseNonisomorphic ψ)
    (hψ_irr : ∀ i, (ψ i).ρ.IsIrreducible)
    (hpacket :
      ((IsScalarTower.toAlgHom ℤ K' (AlgebraicClosure K')).compLeft G) ρ.ρ.character =
        ∑ i, (d i : AlgebraicClosure K') • (ψ i).ρ.character)
    (he : ∀ i, d i = (n : ℕ) * e i)
    (hcoeff_one : ∀ i, e i = 1)
    (hψ_degree : ∀ i, (n : ℕ) ∣ Module.finrank (AlgebraicClosure K') (ψ i)) :
    ∃ (r : ℕ) (_ : 0 < r) (ψ' : Fin r → Rep.{max u v} (AlgebraicClosure K') G),
      (∀ i, FiniteDimensional (AlgebraicClosure K') (ψ' i)) ∧
      PairwiseNonisomorphic ψ' ∧
      (∀ i, (ψ' i).ρ.IsIrreducible) ∧
      ((IsScalarTower.toAlgHom ℤ K' (AlgebraicClosure K')).compLeft G)
          ((((n : ℕ) : K')⁻¹) • ρ.ρ.character) =
        ∑ i, (ψ' i).ρ.character ∧
      ∀ i, (n : ℕ) ∣ Module.finrank (AlgebraicClosure K') (ψ' i) := by
  have hpacket_common :
      ((IsScalarTower.toAlgHom ℤ K' (AlgebraicClosure K')).compLeft G) ρ.ρ.character =
        ∑ i, (n : AlgebraicClosure K') • (ψ i).ρ.character := by
    -- Rewrite each raw multiplicity as the canonical denominator times the unit quotient.
    calc
      ((IsScalarTower.toAlgHom ℤ K' (AlgebraicClosure K')).compLeft G) ρ.ρ.character
          = ∑ i, (d i : AlgebraicClosure K') • (ψ i).ρ.character := hpacket
      _ = ∑ i, (n : AlgebraicClosure K') • (ψ i).ρ.character := by
            refine Finset.sum_congr rfl ?_
            intro i _
            have hdi : d i = (n : ℕ) := by
              calc
                d i = (n : ℕ) * e i := he i
                _ = (n : ℕ) * 1 := by rw [hcoeff_one i]
                _ = (n : ℕ) := Nat.mul_one _
            simp [hdi]
  -- With the visible packet rewritten to common coefficient `n`, the previously proved
  -- reindexing theorem supplies the target multiplicity-free packet.
  exact
    canonical_scaled_character_packet_of_public_common_coeff_local
      (G := G) (ρ := ρ) (n := n) (ψ := ψ)
      hψ_fd hψ_pairwise hψ_irr hpacket_common hψ_degree

/-- Helper for Exercise 12-12.2-6: evaluating the visible packet at `1` rewrites the degree of
the source representation as the weighted sum of the constituent degrees. -/
theorem packet_degree_sum_eq_source_degree_local
    {K' : Type v} [Field K'] [CharZero K']
    (ρ : Rep K' G)
    [FiniteDimensional K' ρ]
    {ι : Type*} [Fintype ι]
    (ψ : ι → Rep.{max u v} (AlgebraicClosure K') G)
    (d : ι → ℕ)
    (hψ_fd : ∀ i, FiniteDimensional (AlgebraicClosure K') (ψ i))
    (hpacket :
      ((IsScalarTower.toAlgHom ℤ K' (AlgebraicClosure K')).compLeft G) ρ.ρ.character =
        ∑ i, (d i : AlgebraicClosure K') • (ψ i).ρ.character) :
    (Module.finrank K' ρ : AlgebraicClosure K') =
      ∑ i, (d i : AlgebraicClosure K') * Module.finrank (AlgebraicClosure K') (ψ i) := by
  -- Evaluating the visible packet at the identity removes the characters and leaves only degrees.
  have hpoint := congrFun hpacket 1
  simp only [Representation.char_one, smul_eq_mul] at hpoint
  simpa using hpoint

/-- Helper for Exercise 12-12.2-6: evaluating the scaled visible packet at `1` rewrites the
scaled source degree as the weighted sum of the constituent degrees. -/
theorem scaled_packet_degree_sum_eq_scaled_source_degree_local
    {K' : Type v} [Field K'] [CharZero K']
    (ρ : Rep K' G)
    [FiniteDimensional K' ρ]
    (n : ℕ+)
    {ι : Type*} [Fintype ι]
    (ψ : ι → Rep.{max u v} (AlgebraicClosure K') G)
    (e : ι → ℕ)
    (hψ_fd : ∀ i, FiniteDimensional (AlgebraicClosure K') (ψ i))
    (hscaled_packet :
      ((IsScalarTower.toAlgHom ℤ K' (AlgebraicClosure K')).compLeft G)
          ((((n : ℕ) : K')⁻¹) • ρ.ρ.character) =
        ∑ i, (e i : AlgebraicClosure K') • (ψ i).ρ.character) :
    (((n : AlgebraicClosure K')⁻¹) * (Module.finrank K' ρ : AlgebraicClosure K')) =
      ∑ i, (e i : AlgebraicClosure K') * Module.finrank (AlgebraicClosure K') (ψ i) := by
  -- The scaled packet identity has the same degree content after evaluation at `1`.
  have hpoint := congrFun hscaled_packet 1
  simp only [Representation.char_one, smul_eq_mul] at hpoint
  simpa [mul_assoc, mul_left_comm, mul_comm] using hpoint

/-- Helper for Exercise 12-12.2-6: the only remaining coefficient-collapse blocker is to show
that the scaled visible packet has one common quotient coefficient. -/
theorem scaled_visible_packet_coeff_constant_of_irreducible_source_local
    {K' : Type v} [Field K'] [CharZero K']
    (ρ : Rep K' G)
    [ρ.ρ.IsIrreducible]
    [FiniteDimensional K' ρ]
    (n : ℕ+)
    {ι : Type*} [Fintype ι]
    (ψ : ι → Rep.{max u v} (AlgebraicClosure K') G)
    (d e : ι → ℕ)
    (hd_pos : ∀ i, 0 < d i)
    (hψ_fd : ∀ i, FiniteDimensional (AlgebraicClosure K') (ψ i))
    (hψ_pairwise : PairwiseNonisomorphic ψ)
    (hψ_irr : ∀ i, (ψ i).ρ.IsIrreducible)
    (hpacket :
      ((IsScalarTower.toAlgHom ℤ K' (AlgebraicClosure K')).compLeft G) ρ.ρ.character =
        ∑ i, (d i : AlgebraicClosure K') • (ψ i).ρ.character)
    (he : ∀ i, d i = (n : ℕ) * e i)
    (hscaled_packet :
      ((IsScalarTower.toAlgHom ℤ K' (AlgebraicClosure K')).compLeft G)
          ((((n : ℕ) : K')⁻¹) • ρ.ρ.character) =
        ∑ i, (e i : AlgebraicClosure K') • (ψ i).ρ.character) :
    ∀ i j, e i = e j := by
  -- Route correction: the actual unresolved step is now isolated in the theorem-local helper
  -- module as the projector descent of one honest orbit block and its complement via the Chapter 6
  -- central-idempotent API.
  simpa using
    Exercise_12_12_2_6.orbit_block_projector_descends_to_source_forces_common_coeff_local
      (G := G) (ρ := ρ) (n := n) (ψ := ψ) (d := d) (e := e)
      hd_pos hψ_fd hψ_pairwise hψ_irr hpacket he hscaled_packet

/-- Helper for Exercise 12-12.2-6: once the theorem-local orbit descent forces the scaled visible
packet coefficients to be constant, the maximality of the canonical denominator forces them to be
exactly `1`. -/
theorem visible_scaled_packet_coeff_one_of_irreducible_source_local
    {K' : Type v} [Field K'] [CharZero K']
    (ρ : Rep K' G)
    [ρ.ρ.IsIrreducible]
    [FiniteDimensional K' ρ]
    (n : ℕ+)
    (hcanon : ((((n : ℕ) : K')⁻¹) • ρ.ρ.character) ∈ R̄[K'](G))
    (hmax :
      ∀ d : ℕ+, ((((d : ℕ) : K')⁻¹) • ρ.ρ.character) ∈ R̄[K'](G) → d ≤ n)
    {ι : Type*} [Fintype ι]
    (ψ : ι → Rep.{max u v} (AlgebraicClosure K') G)
    (d e : ι → ℕ)
    (hd_pos : ∀ i, 0 < d i)
    (hψ_fd : ∀ i, FiniteDimensional (AlgebraicClosure K') (ψ i))
    (hψ_pairwise : PairwiseNonisomorphic ψ)
    (hψ_irr : ∀ i, (ψ i).ρ.IsIrreducible)
    (hpacket :
      ((IsScalarTower.toAlgHom ℤ K' (AlgebraicClosure K')).compLeft G) ρ.ρ.character =
        ∑ i, (d i : AlgebraicClosure K') • (ψ i).ρ.character)
    (he : ∀ i, d i = (n : ℕ) * e i)
    (hscaled_packet :
      ((IsScalarTower.toAlgHom ℤ K' (AlgebraicClosure K')).compLeft G)
          ((((n : ℕ) : K')⁻¹) • ρ.ρ.character) =
        ∑ i, (e i : AlgebraicClosure K') • (ψ i).ρ.character) :
    ∀ i, e i = 1 := by
  have hconst :
      ∀ i j, e i = e j := by
    -- The only remaining source-faithful input is the orbit-collapse step isolated above.
    exact
      scaled_visible_packet_coeff_constant_of_irreducible_source_local
        (G := G) (ρ := ρ) (n := n) (ψ := ψ) (d := d) (e := e)
        hd_pos hψ_fd hψ_pairwise hψ_irr hpacket he hscaled_packet
  intro i
  have hei_pos : 0 < e i := by
    by_contra hei_nonpos
    have hei_zero : e i = 0 := Nat.eq_zero_of_not_pos hei_nonpos
    have hdi_zero : d i = 0 := by
      rw [he i, hei_zero, Nat.mul_zero]
    exact (Nat.lt_irrefl 0) (hdi_zero ▸ hd_pos i)
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
  have hei_one : e i = 1 := by
    rcases hm_dvd_n with ⟨k, hk⟩
    have hone : 1 = e i * k := by
      apply Nat.eq_of_mul_eq_mul_left n.pos
      calc
        (n : ℕ) * 1 = (n : ℕ) := by simp
        _ = (m : ℕ) * k := hk
        _ = ((n : ℕ) * e i) * k := by simp [m]
        _ = (n : ℕ) * (e i * k) := by ac_rfl
    exact Nat.eq_one_of_dvd_one ⟨k, hone⟩
  exact hei_one

/-- Helper for Exercise 12-12.2-6: once the visible scaled packet is known to be unweighted, the
source-faithful degree step still has to descend one isotypic block to obtain `n ∣ dim ψ_i`. -/
theorem visible_packet_constituent_degree_multiple_of_canonical_denominator_local
    {K' : Type v} [Field K'] [CharZero K']
    (ρ : Rep K' G)
    [ρ.ρ.IsIrreducible]
    [FiniteDimensional K' ρ]
    (n : ℕ+)
    (hcanon : ((((n : ℕ) : K')⁻¹) • ρ.ρ.character) ∈ R̄[K'](G))
    (hmax :
      ∀ d : ℕ+, ((((d : ℕ) : K')⁻¹) • ρ.ρ.character) ∈ R̄[K'](G) → d ≤ n)
    {ι : Type*} [Fintype ι]
    (ψ : ι → Rep.{max u v} (AlgebraicClosure K') G)
    (d e : ι → ℕ)
    (hψ_fd : ∀ i, FiniteDimensional (AlgebraicClosure K') (ψ i))
    (hψ_pairwise : PairwiseNonisomorphic ψ)
    (hψ_irr : ∀ i, (ψ i).ρ.IsIrreducible)
    (hpacket :
      ((IsScalarTower.toAlgHom ℤ K' (AlgebraicClosure K')).compLeft G) ρ.ρ.character =
        ∑ i, (d i : AlgebraicClosure K') • (ψ i).ρ.character)
    (he : ∀ i, d i = (n : ℕ) * e i)
    (hscaled_packet :
      ((IsScalarTower.toAlgHom ℤ K' (AlgebraicClosure K')).compLeft G)
          ((((n : ℕ) : K')⁻¹) • ρ.ρ.character) =
        ∑ i, (e i : AlgebraicClosure K') • (ψ i).ρ.character)
    (hcoeff_one : ∀ i, e i = 1) :
    ∀ i, (n : ℕ) ∣ Module.finrank (AlgebraicClosure K') (ψ i) := by
  -- Route correction: the honest isotypic block has already been isolated. The unresolved part is
  -- now isolated in the helper module as the stabilizer-fixed-field projector descent for the
  -- central idempotent attached to one constituent.
  simpa using
    Exercise_12_12_2_6.isotypic_block_projector_descends_to_stabilizer_forces_degree_multiple_local
      (G := G) (ρ := ρ) (n := n) hcanon hmax
      (ψ := ψ) (d := d) (e := e)
      hψ_fd hψ_pairwise hψ_irr hpacket he hscaled_packet hcoeff_one

/-- Helper for Exercise 12-12.2-6: the canonical source denominator yields LinearRepresentations_Serre_1977's packet
`χ_i / m_i = ∑_σ ψ_{i,σ}` after scalar extension to the algebraic closure. -/
theorem canonical_scaled_character_packet_local
    {K' : Type v} [Field K'] [CharZero K']
    (ρ : Rep K' G)
    [ρ.ρ.IsIrreducible]
    (n : ℕ+)
    (hcanon : ((((n : ℕ) : K')⁻¹) • ρ.ρ.character) ∈ R̄[K'](G))
    (hmax :
      ∀ d : ℕ+, ((((d : ℕ) : K')⁻¹) • ρ.ρ.character) ∈ R̄[K'](G) → d ≤ n) :
    ∃ (r : ℕ) (_ : 0 < r) (ψ : Fin r → Rep.{max u v} (AlgebraicClosure K') G),
      (∀ i, FiniteDimensional (AlgebraicClosure K') (ψ i)) ∧
      PairwiseNonisomorphic ψ ∧
      (∀ i, (ψ i).ρ.IsIrreducible) ∧
      ((IsScalarTower.toAlgHom ℤ K' (AlgebraicClosure K')).compLeft G)
          ((((n : ℕ) : K')⁻¹) • ρ.ρ.character) =
        ∑ i, (ψ i).ρ.character ∧
      ∀ i, (n : ℕ) ∣ Module.finrank (AlgebraicClosure K') (ψ i) := by
  classical
  -- Route correction: the old tensor/universe detour is no longer the governing argument here.
  -- The source route is closure-first: build the algebraic-closure packet for the canonical
  -- denominator `n`, regroup the scalar-extension constituents into one Galois packet, prove the
  -- resulting orbit multiplicity is exactly `n`, and then read off the constituent degrees.
  letI : FiniteDimensional K' ρ :=
    Representation.IsIrreducible.finiteDimensional_of_finite ρ.ρ
  have hmap_char :
      (Representation.scalarExtension (k := AlgebraicClosure K') ρ.ρ).character =
        ((IsScalarTower.toAlgHom ℤ K' (AlgebraicClosure K')).compLeft G) ρ.ρ.character :=
    scalarExtension_character_eq_map_algClosure_local (G := G) ρ
  have hscaled_closure :
      ((IsScalarTower.toAlgHom ℤ K' (AlgebraicClosure K')).compLeft G)
          ((((n : ℕ) : K')⁻¹) • ρ.ρ.character) ∈
        R[AlgebraicClosure K'](G) := by
    -- Unpack the canonical source denominator witness into the algebraic-closure owner before
    -- starting the packet analysis.
    exact
      (mem_overlineCharacterRingInExtension_iff K' (AlgebraicClosure K')
        ((((n : ℕ) : K')⁻¹) • ρ.ρ.character)).1 hcanon
  obtain ⟨ι, _, ψ, d, hd_pos, hψ_fd, hψ_pairwise, hψ_irr, hpacket⟩ :=
    scalar_extension_public_packet_visible_adapter_local
      (G := G) (K' := K') ρ
  have hcoeff_div : ∀ i, (n : ℕ) ∣ d i := by
    -- The visible packet is now in the right source-facing form, so the coefficient-divisibility
    -- lemma applies directly before the final orbit-collapse step.
    exact
      canonical_denominator_dvd_packet_coefficient_universe_local
        (G := G) (ρ := ρ) (n := n) hcanon
        (ψ := ψ) (d := d) hψ_fd hψ_pairwise hψ_irr hpacket
  obtain ⟨e, he, hscaled_packet⟩ :=
    scaled_visible_packet_of_canonical_denominator_local
      (G := G) (ρ := ρ) (n := n) (ψ := ψ) (d := d) hpacket hcoeff_div
  -- TODO: finish the source-faithful orbit-collapse step on the visible packet.
  -- The stabilized frontier is now:
  -- 1. `hpacket` is already the visible algebraic-closure packet
  --    `map χ_ρ = ∑ i, d i • χ_(ψ i)`.
  -- 2. `hcoeff_div` and `hscaled_packet` refine this to the scaled packet
  --    `map ((1 / n) • χ_ρ) = ∑ i, e i • χ_(ψ i)` with exact quotient coefficients
  --    `d i = n * e i`.
  -- 3. The remaining theorem-local work is to show LinearRepresentations_Serre_1977's packet consists of one Galois orbit,
  --    hence every quotient coefficient `e i` is `1`.
  -- 4. Once `e i = 1` for all `i`, `canonical_scaled_character_packet_of_public_common_coeff_local`
  --    and the source degree argument finish the theorem.
  -- The remaining blocker is therefore the theorem-local orbit-collapse and degree-transfer
  -- layer, no longer the visible-packet adapter itself.
  let _ : Type := ι
  let _ : ι → Rep.{max u v} (AlgebraicClosure K') G := ψ
  let _ : ι → ℕ := d
  let _ : ∀ i, 0 < d i := hd_pos
  let _ : ∀ i, FiniteDimensional (AlgebraicClosure K') (ψ i) := hψ_fd
  let _ : PairwiseNonisomorphic ψ := hψ_pairwise
  let _ : ∀ i, (ψ i).ρ.IsIrreducible := hψ_irr
  let _ :
      ((IsScalarTower.toAlgHom ℤ K' (AlgebraicClosure K')).compLeft G) ρ.ρ.character =
        ∑ i, (d i : AlgebraicClosure K') • (ψ i).ρ.character := hpacket
  let _ : ∀ i, (n : ℕ) ∣ d i := hcoeff_div
  let _ : ι → ℕ := e
  let _ : ∀ i, d i = (n : ℕ) * e i := he
  let _ :
      ((IsScalarTower.toAlgHom ℤ K' (AlgebraicClosure K')).compLeft G)
          ((((n : ℕ) : K')⁻¹) • ρ.ρ.character) =
        ∑ i, (e i : AlgebraicClosure K') • (ψ i).ρ.character := hscaled_packet
  have hcoeff_one : ∀ i, e i = 1 := by
    -- Reduce the orbit-collapse step to the dedicated theorem-local helper so the main theorem
    -- stays aligned with LinearRepresentations_Serre_1977's closure-first packet skeleton.
    exact
      visible_scaled_packet_coeff_one_of_irreducible_source_local
        (G := G) (ρ := ρ) (n := n) hcanon hmax
        (ψ := ψ) (d := d) (e := e) hd_pos
        hψ_fd hψ_pairwise hψ_irr hpacket he hscaled_packet
  have hψ_degree : ∀ i, (n : ℕ) ∣ Module.finrank (AlgebraicClosure K') (ψ i) := by
    -- With the quotient coefficients isolated in `hcoeff_one`, only the source-faithful
    -- isotypic-block descent remains.
    exact
      visible_packet_constituent_degree_multiple_of_canonical_denominator_local
        (G := G) (ρ := ρ) (n := n) hcanon hmax
        (ψ := ψ) (d := d) (e := e)
        hψ_fd hψ_pairwise hψ_irr hpacket he hscaled_packet hcoeff_one
  exact
    canonical_scaled_character_packet_of_scaled_visible_packet_coeff_one_local
      (G := G) (ρ := ρ) (n := n) (ψ := ψ) (d := d) (e := e)
      hψ_fd hψ_pairwise hψ_irr hpacket he hcoeff_one hψ_degree

/-- Helper for Exercise 12-12.2-6: Proposition `17` over an algebraically closed field should send
the degree of an irreducible constituent to the center index. -/
theorem finrank_dvd_center_index_over_algClosed_local
    {L : Type w} [Field L] [CharZero L] [IsAlgClosed L]
    (σ : Rep.{max u w} L G)
    [FiniteDimensional L σ]
    [σ.ρ.IsIrreducible] :
    Module.finrank L σ ∣ (Subgroup.center G).index := by
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
  -- Rewrite the tensor-power degree and the subgroup index into LinearRepresentations_Serre_1977's arithmetic identity.
  simpa [H, _root_.Representation.tensor_power_finrank_field_local,
    product_one_center_subgroup_index] using hdiv

end FieldPart

end Representation
