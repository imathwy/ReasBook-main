import LinearRepresentations_Serre_1977.Serre.Chap01.Definition_1_1_2_1
import LinearRepresentations_Serre_1977.Serre.Chap02.Proposition_2_2_2_1
import LinearRepresentations_Serre_1977.Serre.Chap03.Theorem_3_3_2_1
import LinearRepresentations_Serre_1977.Serre.Chap06.Corollary_6_6_5_4
import LinearRepresentations_Serre_1977.Serre.Chap06.Exercise_6_6_3_3
import LinearRepresentations_Serre_1977.Serre.Chap06.Proposition_6_6_5_5
import LinearRepresentations_Serre_1977.Serre.Chap10.Theorem_10_10_5_2
import LinearRepresentations_Serre_1977.Serre.Chap12.CharacterRingOverFieldScalarExtension
import LinearRepresentations_Serre_1977.Serre.Chap12.Exercise_12_12_2_3.API
import LinearRepresentations_Serre_1977.Serre.Chap12.Exercise_12_12_2_6.Index

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

-- Route correction: the packet-transport and complex-realization support now come through the
-- theorem-local index, so the main file keeps only the field-side development and the active
-- theorem statement.

end Exercise_12_12_2_6

omit [Finite G] in
/-- Helper for Exercise 12-12.2-6: evaluating an honest isotypic-fiber character identity at `1`
turns it into the corresponding degree sum identity. -/
private theorem isotypic_fiber_degree_sum_from_character_local
    {K1 : Type v} [Field K1] [CharZero K1]
    (ρ : Rep K1 G)
    [FiniteDimensional K1 ρ]
    {ι : Type*}
    (ψ : ι → Rep.{max u v} (AlgebraicClosure K1) G)
    (a : ℕ)
    (σ : Fin a → Subrepresentation
      (Representation.scalarExtension (k := AlgebraicClosure K1) ρ.ρ))
    (S : ι → Finset (Fin a))
    (d : ι → ℕ)
    (hψ_fd : ∀ i, FiniteDimensional (AlgebraicClosure K1) (ψ i))
    (hfiber_char :
      ∀ i,
        Finset.sum
            (S i)
            (fun j ↦ ((σ j).toRepresentation).character) =
          (d i : AlgebraicClosure K1) • (ψ i).ρ.character) :
    ∀ i,
      ((Finset.sum (S i)
          (fun j ↦ Module.finrank (AlgebraicClosure K1) ↥((σ j).toSubmodule)) : ℕ) :
          AlgebraicClosure K1) =
        (d i : AlgebraicClosure K1) *
          (Module.finrank (AlgebraicClosure K1) (ψ i) : AlgebraicClosure K1) := by
  intro i
  letI : FiniteDimensional (AlgebraicClosure K1) (ψ i) := hψ_fd i
  -- Evaluate the fiber character identity at the group identity to replace characters by degrees.
  simpa [Representation.char_one, smul_eq_mul] using congrFun (hfiber_char i) 1

/-- Helper for Exercise 12-12.2-6: every honest isotypic fiber is nonempty because its degree sum
is a positive multiple of the degree of an irreducible constituent. -/
private theorem isotypic_fiber_nonempty_of_positive_multiplicity_local
    {K1 : Type v} [Field K1] [CharZero K1]
    (ρ : Rep K1 G)
    [FiniteDimensional K1 ρ]
    {ι : Type*}
    (ψ : ι → Rep.{max u v} (AlgebraicClosure K1) G)
    (a : ℕ)
    (σ : Fin a → Subrepresentation
      (Representation.scalarExtension (k := AlgebraicClosure K1) ρ.ρ))
    (S : ι → Finset (Fin a))
    (d : ι → ℕ)
    (hd_pos : ∀ i, 0 < d i)
    (hψ_fd : ∀ i, FiniteDimensional (AlgebraicClosure K1) (ψ i))
    (hψ_irr : ∀ i, (ψ i).ρ.IsIrreducible)
    (hfiber_char :
      ∀ i,
        Finset.sum
            (S i)
            (fun j ↦ ((σ j).toRepresentation).character) =
          (d i : AlgebraicClosure K1) • (ψ i).ρ.character) :
    ∀ i, (S i).Nonempty := by
  intro i
  letI : FiniteDimensional (AlgebraicClosure K1) (ψ i) := hψ_fd i
  letI : (ψ i).ρ.IsIrreducible := hψ_irr i
  by_contra hSi_empty
  have hfiber_degree :=
    isotypic_fiber_degree_sum_from_character_local
      (G := G) (ρ := ρ) (ψ := ψ) (a := a) (σ := σ) (S := S) (d := d) hψ_fd hfiber_char i
  have hd_ne : (d i : AlgebraicClosure K1) ≠ 0 := by
    exact Nat.cast_ne_zero.mpr (Nat.ne_of_gt (hd_pos i))
  have hdim_ne :
      (Module.finrank (AlgebraicClosure K1) (ψ i) : AlgebraicClosure K1) ≠ 0 := by
    exact Nat.cast_ne_zero.mpr
      (Nat.ne_of_gt (irreducible_rep_finrank_pos_local (G := G) (V := ψ i)))
  have hfiber_degree_zero :
      (((Finset.sum (S i)
          (fun j ↦ Module.finrank (AlgebraicClosure K1) ↥((σ j).toSubmodule)) : ℕ) :
          AlgebraicClosure K1)) = 0 := by
    -- If the fiber were empty, its degree sum would vanish.
    simp [Finset.not_nonempty_iff_eq_empty.mp hSi_empty]
  have hmul_zero :
      (d i : AlgebraicClosure K1) *
          (Module.finrank (AlgebraicClosure K1) (ψ i) : AlgebraicClosure K1) =
        0 := by
    -- Compare the positive target degree with the vanishing empty-fiber degree sum.
    exact hfiber_degree_zero ▸ hfiber_degree.symm
  exact (mul_ne_zero hd_ne hdim_ne) hmul_zero

omit [Finite G] in
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
  letI : FiniteDimensional (AlgebraicClosure K1) (ψ i) := hψ_fd i
  -- Evaluate the honest-fiber character identity at `1` to convert characters into degrees.
  simpa [Representation.char_one, smul_eq_mul] using congrFun (hfiber_char i) 1

/-- Helper for Exercise 12-12.2-6: once the honest `i`-th fiber has character `n • χ_(ψ i)`,
that fiber contains exactly `n` irreducible summands. -/
private theorem canonical_isotypic_fiber_card_eq_denominator_local
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
    (hψ_irr : ∀ i, (ψ i).ρ.IsIrreducible)
    (hσ_irr : ∀ j, ((σ j).toRepresentation).IsIrreducible)
    (hS : ∀ i j, j ∈ S i ↔ Nonempty (((σ j).toRepresentation).Equiv (ψ i).ρ))
    (hfiber_char :
      ∀ i,
        Finset.sum
            (S i)
            (fun j ↦ ((σ j).toRepresentation).character) =
          (n : AlgebraicClosure K1) • (ψ i).ρ.character) :
    ∀ i, (S i).card = n := by
  intro i
  letI : FiniteDimensional (AlgebraicClosure K1) (ψ i) := hψ_fd i
  letI : (ψ i).ρ.IsIrreducible := hψ_irr i
  have hfiber_degree :=
    actual_scalar_extension_isotypic_fiber_degree_sum_eq_local
      (G := G) (ρ := ρ) (n := n) (ψ := ψ) (a := a) (σ := σ) (S := S) hψ_fd hfiber_char i
  have hsum_eq :
      (Finset.sum (S i)
          (fun j ↦ Module.finrank (AlgebraicClosure K1) ↥((σ j).toSubmodule)) : ℕ) =
        (S i).card * Module.finrank (AlgebraicClosure K1) (ψ i) := by
    -- Every summand in the honest `i`-th fiber is isomorphic to `ψ i`, so the degree sum is a
    -- constant-cardinality multiple of `dim ψ i`.
    calc
      (Finset.sum (S i)
          (fun j ↦ Module.finrank (AlgebraicClosure K1) ↥((σ j).toSubmodule)) : ℕ)
          =
        Finset.sum (S i) (fun _ ↦ Module.finrank (AlgebraicClosure K1) (ψ i)) := by
            refine Finset.sum_congr rfl ?_
            intro j hj
            letI : ((σ j).toRepresentation).IsIrreducible := hσ_irr j
            letI : FiniteDimensional (AlgebraicClosure K1) ↥((σ j).toSubmodule) :=
              Representation.IsIrreducible.finiteDimensional_of_finite
                (ρ := (σ j).toRepresentation)
            have hj_iso : Nonempty (((σ j).toRepresentation).Equiv (ψ i).ρ) := (hS i j).mp hj
            rcases hj_iso with ⟨eIso⟩
            have hdim_cast :
                (Module.finrank (AlgebraicClosure K1) ↥((σ j).toSubmodule) :
                    AlgebraicClosure K1) =
                  (Module.finrank (AlgebraicClosure K1) (ψ i) : AlgebraicClosure K1) := by
              simpa [Representation.char_one] using congrFun (Representation.char_iso eIso) 1
            exact Nat.cast_injective hdim_cast
      _ = (S i).card * Module.finrank (AlgebraicClosure K1) (ψ i) := by
            simp
  have hmul_eq :
      (S i).card * Module.finrank (AlgebraicClosure K1) (ψ i) =
        (n : ℕ) * Module.finrank (AlgebraicClosure K1) (ψ i) := by
    have hmul_eq_cast :
        (((S i).card * Module.finrank (AlgebraicClosure K1) (ψ i) : ℕ) :
            AlgebraicClosure K1) =
          (((n : ℕ) * Module.finrank (AlgebraicClosure K1) (ψ i) : ℕ) :
            AlgebraicClosure K1) := by
      calc
        (((S i).card * Module.finrank (AlgebraicClosure K1) (ψ i) : ℕ) :
            AlgebraicClosure K1)
            =
          (((Finset.sum (S i)
              (fun j ↦ Module.finrank (AlgebraicClosure K1) ↥((σ j).toSubmodule)) : ℕ)) :
                AlgebraicClosure K1) := by
              rw [hsum_eq]
        _ = (n : AlgebraicClosure K1) *
            (Module.finrank (AlgebraicClosure K1) (ψ i) : AlgebraicClosure K1) := hfiber_degree
        _ =
          (((n : ℕ) * Module.finrank (AlgebraicClosure K1) (ψ i) : ℕ) :
              AlgebraicClosure K1) := by
              simp
    exact Nat.cast_injective hmul_eq_cast
  have hdim_pos : 0 < Module.finrank (AlgebraicClosure K1) (ψ i) := by
    exact irreducible_rep_finrank_pos_local (G := G) (V := ψ i)
  exact Nat.eq_of_mul_eq_mul_right hdim_pos hmul_eq

/-- Helper for Exercise 12-12.2-6: after the visible quotient coefficients collapse to `1`, the
honest isotypic fibers already realize the canonical multiple `n • χ_(ψ i)` and are nonempty. -/
private theorem canonicalMultipleHonestFiberSetup_local
    {K1 : Type v} [Field K1] [CharZero K1]
    (ρ : Rep K1 G)
    [FiniteDimensional K1 ρ]
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
    (hcoeff_one : ∀ i, e i = 1) :
    ∃ (a : ℕ) (σ : Fin a → Subrepresentation
        (Representation.scalarExtension (k := AlgebraicClosure K1) ρ.ρ))
      (S : ι → Finset (Fin a)),
      DirectSum.IsInternal (fun j ↦ (σ j).toSubmodule) ∧
      (Representation.scalarExtension (k := AlgebraicClosure K1) ρ.ρ).character =
        ∑ j, ((σ j).toRepresentation).character ∧
      (∀ j, ((σ j).toRepresentation).IsIrreducible) ∧
      (∀ i j, j ∈ S i ↔ Nonempty (((σ j).toRepresentation).Equiv (ψ i).ρ)) ∧
      (∀ i, (S i).Nonempty) ∧
      ∀ i,
        Finset.sum
            (S i)
            (fun j ↦ ((σ j).toRepresentation).character) =
          (n : AlgebraicClosure K1) • (ψ i).ρ.character := by
  obtain ⟨a, σ, S, hinternal, hσchar, hσirr, hS, hcanonical_fiber⟩ :=
    actual_scalar_extension_isotypic_fiber_character_eq_canonical_multiple_local
      (G := G) (ρ := ρ) (n := n) (ψ := ψ) (d := d) (e := e)
      hψ_fd hψ_pairwise hψ_irr hpacket he hcoeff_one
  have hS_nonempty : ∀ i, (S i).Nonempty := by
    -- The canonical multiple is the positive constant `n`, so each honest fiber must contain a
    -- visible irreducible summand.
    exact
      isotypic_fiber_nonempty_of_positive_multiplicity_local
        (G := G) (ρ := ρ) (ψ := ψ) (a := a) (σ := σ) (S := S)
        (d := fun _ : ι ↦ (n : ℕ)) (hd_pos := fun _ ↦ n.pos)
        hψ_fd hψ_irr hcanonical_fiber
  exact ⟨a, σ, S, hinternal, hσchar, hσirr, hS, hS_nonempty, hcanonical_fiber⟩

/-- Helper for Exercise 12-12.2-6: after the quotient coefficients collapse to `1`, each honest
isotypic fiber contains exactly `n` irreducible summands. This packages the canonical fiber
decomposition with the cardinality count that the remaining stabilizer step would need, without
rebuilding the degree comparison locally. -/
private theorem canonicalMultipleHonestFiberCardSetup_local
    {K1 : Type v} [Field K1] [CharZero K1]
    (ρ : Rep K1 G)
    [FiniteDimensional K1 ρ]
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
    (hcoeff_one : ∀ i, e i = 1) :
    ∃ (a : ℕ) (σ : Fin a → Subrepresentation
        (Representation.scalarExtension (k := AlgebraicClosure K1) ρ.ρ))
      (S : ι → Finset (Fin a)),
      DirectSum.IsInternal (fun j ↦ (σ j).toSubmodule) ∧
      (Representation.scalarExtension (k := AlgebraicClosure K1) ρ.ρ).character =
        ∑ j, ((σ j).toRepresentation).character ∧
      (∀ j, ((σ j).toRepresentation).IsIrreducible) ∧
      (∀ i j, j ∈ S i ↔ Nonempty (((σ j).toRepresentation).Equiv (ψ i).ρ)) ∧
      (∀ i, (S i).Nonempty) ∧
      (∀ i,
        Finset.sum
            (S i)
            (fun j ↦ ((σ j).toRepresentation).character) =
          (n : AlgebraicClosure K1) • (ψ i).ρ.character) ∧
      ∀ i, (S i).card = n := by
  obtain ⟨a, σ, S, hinternal, hσchar, hσirr, hS, hS_nonempty, hcanonical_fiber⟩ :=
    canonicalMultipleHonestFiberSetup_local
      (G := G) (ρ := ρ) (n := n) (ψ := ψ) (d := d) (e := e)
      hψ_fd hψ_pairwise hψ_irr hpacket he hcoeff_one
  have hcard : ∀ i, (S i).card = n := by
    -- Evaluate the canonical fiber identity at `1` and compare degrees to convert the character
    -- multiplicity `n` into an honest count of irreducible summands.
    exact
      canonical_isotypic_fiber_card_eq_denominator_local
        (G := G) (ρ := ρ) (n := n) (ψ := ψ) (a := a) (σ := σ) (S := S)
        hψ_fd hψ_irr hσirr hS hcanonical_fiber
  exact
    ⟨a, σ, S, hinternal, hσchar, hσirr, hS, hS_nonempty, hcanonical_fiber, hcard⟩

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

/-- Helper for Exercise 12-12.2-6: once one visible packet constituent produces a fixed-field
block of degree `n * dim ψ_i`, the final center-index divisibility follows immediately by
transitivity. -/
private theorem canonicalDenominatorDvdCenterIndex_fromBlockDegree_local
    {K1 : Type v} [Field K1] [CharZero K1]
    (n : ℕ+)
    {r : ℕ}
    (hr : 0 < r)
    (ψ : Fin r → Rep.{max u v} (AlgebraicClosure K1) G)
    (hblock_degree :
      ∀ i, ((n : ℕ) * Module.finrank (AlgebraicClosure K1) (ψ i)) ∣
        (Subgroup.center G).index) :
    (n : ℕ) ∣ (Subgroup.center G).index := by
  let i0 : Fin r := ⟨0, hr⟩
  -- Route correction: the source-faithful fixed-field theorem only needs to land in the block
  -- degree `n * dim ψ_i`; the final `n ∣ [G : Z(G)]` step is then a pure divisibility cleanup.
  exact
    dvd_trans
      (dvd_mul_of_dvd_left (dvd_refl (n : ℕ))
        (Module.finrank (AlgebraicClosure K1) (ψ i0)))
      (hblock_degree i0)

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
  classical
  letI : FiniteDimensional K1 ρ :=
    Representation.IsIrreducible.finiteDimensional_of_finite ρ.ρ
  obtain ⟨ι, _, ψ, d, e, hd_pos, hψ_fd, hψ_pairwise, hψ_irr, hpacket, _hcoeff_div, he,
      hscaled_packet⟩ :=
    canonical_scaled_character_visible_packet_frontier_local
      (G := G) (ρ := ρ) (n := n) hcanon hmax
  have hcoeff_one : ∀ i, e i = 1 := by
    -- First collapse the visible packet coefficients to Serre's canonical unweighted packet.
    exact
      visible_scaled_packet_coeff_one_of_irreducible_source_local
        (G := G) (ρ := ρ) (n := n) hcanon hmax
        (ψ := ψ) (d := d) (e := e) hd_pos
        hψ_fd hψ_pairwise hψ_irr hpacket he hscaled_packet
  have hn_degree :
      ∀ i, (n : ℕ) ∣ Module.finrank (AlgebraicClosure K1) (ψ i) := by
    exact
      visiblePacketConstituentDenominatorDvdDegree_local
        (G := G) (ρ := ρ) (n := n) hcanon hmax
        (ψ := ψ) (d := d) (e := e)
        hψ_fd hψ_pairwise hψ_irr hpacket he hscaled_packet hcoeff_one
  have hι_nonempty : Nonempty ι := by
    -- The scaled visible packet cannot be empty because its value at `1` is the nonzero scaled
    -- degree of the irreducible source representation.
    classical
    by_contra hι_empty
    letI : IsEmpty ι := not_nonempty_iff.mp hι_empty
    have hpoint :
        ((n : AlgebraicClosure K1)⁻¹) *
            (Module.finrank K1 ρ : AlgebraicClosure K1) = 0 := by
      simpa [Representation.char_one, smul_eq_mul] using congrFun hscaled_packet 1
    have hn_ne : (n : AlgebraicClosure K1) ≠ 0 := by
      exact Nat.cast_ne_zero.mpr n.ne_zero
    have hfinrank_pos : 0 < Module.finrank K1 ρ := by
      letI : Nontrivial ρ := by
        by_contra hρ_trivial
        letI : Subsingleton ρ := not_nontrivial_iff_subsingleton.mp hρ_trivial
        have hbot_ne_top : (⊥ : Subrepresentation ρ.ρ) ≠ ⊤ := by
          exact bot_ne_top
        have hbot : (⊥ : Subrepresentation ρ.ρ) = ⊤ := by
          apply Subrepresentation.toSubmodule_injective
          ext x
          constructor
          · intro _
            trivial
          · intro _
            change x = 0
            exact Subsingleton.elim x 0
        exact hbot_ne_top hbot
      exact Module.finrank_pos
    have hfinrank_ne :
        (Module.finrank K1 ρ : AlgebraicClosure K1) ≠ 0 := by
      exact Nat.cast_ne_zero.mpr
        (Nat.ne_of_gt hfinrank_pos)
    exact (mul_ne_zero (inv_ne_zero hn_ne) hfinrank_ne) hpoint
  obtain ⟨i0⟩ := hι_nonempty
  letI : FiniteDimensional (AlgebraicClosure K1) (ψ i0) := hψ_fd i0
  letI : (ψ i0).ρ.IsIrreducible := hψ_irr i0
  have hdegree_center :
      Module.finrank (AlgebraicClosure K1) (ψ i0) ∣ (Subgroup.center G).index :=
    finrank_dvd_center_index_over_algClosed_shadow_local (G := G) (ψ i0)
  exact dvd_trans (hn_degree i0) hdegree_center

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


omit [Finite G] in
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
