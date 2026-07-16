import Mathlib
import LinearRepresentations_Serre_1977.Serre.Chap02.Proposition_2_2_2_1
import LinearRepresentations_Serre_1977.Serre.Chap03.Theorem_3_3_2_1
import LinearRepresentations_Serre_1977.Serre.Chap06.Corollary_6_6_5_4
import LinearRepresentations_Serre_1977.Serre.Chap06.Proposition_6_6_5_5
import LinearRepresentations_Serre_1977.Serre.Chap12.Exercise_12_12_2_3.API
import LinearRepresentations_Serre_1977.Serre.Chap12.Exercise_12_12_2_6.CharacterBasisCoefficients
import LinearRepresentations_Serre_1977.Serre.Chap12.Exercise_12_12_2_6.ComplexMinimalRealization
import LinearRepresentations_Serre_1977.Serre.Chap12.Exercise_12_12_2_6.ExternalTensorUniverseBridge
import LinearRepresentations_Serre_1977.Serre.Chap12.Exercise_12_12_2_6.FieldDenominatorDescent
import LinearRepresentations_Serre_1977.Serre.Chap12.Exercise_12_12_2_6.FieldDenominatorPrelude
import LinearRepresentations_Serre_1977.Serre.Chap12.Exercise_12_12_2_6.FieldTensorCenterBridge
import LinearRepresentations_Serre_1977.Serre.Chap12.Exercise_12_12_2_6.ScalarExtensionBlockProjectors
import LinearRepresentations_Serre_1977.Serre.Chap12.Exercise_12_12_2_6.ScalarExtensionConstituents
import LinearRepresentations_Serre_1977.Serre.Chap12.Exercise_12_12_2_6.ScalarExtensionPackets
import LinearRepresentations_Serre_1977.Serre.Chap12.Exercise_12_12_2_6.ScalarExtensionPairing
import LinearRepresentations_Serre_1977.Serre.Chap12.Proposition_12_12_2_1
import LinearRepresentations_Serre_1977.Serre.Chap12.Theorem_12_12_3_1

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

namespace Exercise_12_12_2_6

section FieldPart

variable {G : Type u} [Group G] [Finite G]

local instance instFintypeGExercise_12_12_2_6_packet_projector_descent : Fintype G :=
  Fintype.ofFinite G

/-- Helper for Exercise 12-12.2-6: once the visible quotient coefficients are constant, the
canonical denominator maximality argument forces that common value to be exactly `1`. -/
private theorem visible_scaled_packet_coeff_one_of_common_coeff_projector_local
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

/-- Helper for Exercise 12-12.2-6: this theorem-local seam isolates Serre's orbit-projector
descent step at exactly the visible packet frontier used by the target file. -/
theorem visible_scaled_packet_coeff_one_seam_local
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
    ∀ i, e i = 1 := by
  have hconst : ∀ i j, e i = e j := by
    -- The orbit-projector descent is now owned by the block-projector support theorem.
    exact
      Exercise_12_12_2_6.orbit_block_projector_descends_to_source_forces_common_coeff_local
        (G := G) (ρ := ρ) (n := n) hcanon hmax
        (ψ := ψ) (d := d) (e := e)
        hd_pos hψ_fd hψ_pairwise hψ_irr hpacket he hscaled_packet
  exact
    visible_scaled_packet_coeff_one_of_common_coeff_projector_local
      (G := G) (ρ := ρ) (n := n) hcanon hmax
      (ψ := ψ) (d := d) (e := e) hd_pos
      hψ_fd hψ_pairwise hψ_irr hpacket he hconst

/-- Helper for Exercise 12-12.2-6: after the coefficient-collapse step `e_i = 1`, Serre's
division-algebra degree comparison forces the canonical denominator to divide every visible
constituent degree. -/
theorem stabilizer_fixedField_degree_divisibility_seam_local
    {K1 : Type v} [Field K1] [CharZero K1]
    (ρ : Rep K1 G)
    [ρ.ρ.IsIrreducible]
    [FiniteDimensional K1 ρ]
    (n : ℕ+)
    (hcanon : ((((n : ℕ) : K1)⁻¹) • ρ.ρ.character) ∈ R̄[K1](G))
    (hmax :
      ∀ d' : ℕ+, ((((d' : ℕ) : K1)⁻¹) • ρ.ρ.character) ∈ R̄[K1](G) → d' ≤ n)
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
  exact
    Exercise_12_12_2_6.isotypicBlockProjectorDescendsToStabilizer_forcesDenominatorDegree_local
      (G := G) (ρ := ρ) (n := n) hcanon hmax
      (ψ := ψ) (d := d) (e := e)
      hψ_fd hψ_pairwise hψ_irr hpacket he hscaled_packet hcoeff_one

end FieldPart

end Exercise_12_12_2_6

end Representation
