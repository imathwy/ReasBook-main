import Mathlib
import LinearRepresentations_Serre_1977.Serre.Chap02.Theorem_2_2_3_5
import LinearRepresentations_Serre_1977.Serre.Chap03.Theorem_3_3_2_1
import LinearRepresentations_Serre_1977.Serre.Chap01.Theorem_1_1_4_2
import LinearRepresentations_Serre_1977.Serre.RepresentationTheory.RealizableOver

noncomputable section

open scoped BigOperators
open scoped Representation
open scoped MonoidAlgebra

universe u v w

namespace Representation

open scoped DirectSum
open CategoryTheory

namespace Exercise_12_12_2_6

section ExtensionPart

variable {G : Type u} [Group G] [Finite G]

local instance instFintypeGExercise_12_12_2_6_complex : Fintype G := Fintype.ofFinite G

/-- Helper for Exercise 12-12.2-6: an internal direct-sum decomposition computes the character as
the sum of the constituent characters. -/
private theorem character_eq_sum_character_of_internal_decomposition_support_local
    {K : Type v} [Field K]
    {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ρ : Representation K G V)
    (σ : ι → Subrepresentation ρ)
    (hinternal : DirectSum.IsInternal (fun i ↦ (σ i).toSubmodule)) :
    ρ.character = ∑ i, ((σ i).toRepresentation).character := by
  -- Decompose the trace along the internal direct sum of the chosen irreducible summands.
  ext g
  simpa [Representation.character] using
    (LinearMap.trace_eq_sum_trace_restrict
      (R := K) (M := V) (N := fun i ↦ (σ i).toSubmodule) hinternal
      (f := ρ g) (hf := fun i ↦ (σ i).apply_mem_toSubmodule g))

/-- Helper for Exercise 12-12.2-6: the canonical owner-submodule bridge from Chapter 1 identifies
the underlying `K`-submodule of `Subrepresentation.ofSubmodule'`. -/
private theorem toSubmodule_ofSubmodule'_eq_restrictScalars_support_local
    {K : Type v} [Field K]
    {V : Type*} [AddCommGroup V] [Module K V]
    (ρ : Representation K G V) (N : Submodule K[G] ρ.asModule) :
    (Subrepresentation.ofSubmodule' N).toSubmodule = N.restrictScalars K := rfl

/-- Helper for Exercise 12-12.2-6: transporting the Chapter 1 simple-submodule decomposition
across `Subrepresentation.ofSubmodule'` produces a subtype-indexed family of honest
subrepresentations whose underlying `K`-submodules are independent and span the whole carrier. -/
private theorem iSupIndep_and_iSup_top_of_subtype_ofSubmodule'_family_support_local
    {K : Type v} [Field K]
    {V : Type*} [AddCommGroup V] [Module K V]
    (ρ : Representation K G V) (s : Set (Submodule K[G] ρ.asModule))
    (hs_indep : sSupIndep s) (hs_top : sSup s = ⊤) :
    iSupIndep (fun i : s ↦ (Subrepresentation.ofSubmodule' i.1).toSubmodule) ∧
      (⨆ i : s, (Subrepresentation.ofSubmodule' i.1).toSubmodule) = ⊤ := by
  -- Move the Chapter 1 simple owner-submodule decomposition to honest `K`-subrepresentations.
  have hs_indep' : iSupIndep (fun i : s ↦ (i : Submodule K[G] ρ.asModule)) :=
    (sSupIndep_iff s).mp hs_indep
  have hσ_indep :
      iSupIndep (fun i : s ↦ Submodule.restrictScalars K (i : Submodule K[G] ρ.asModule)) := by
    rw [iSupIndep] at hs_indep'
    rw [iSupIndep]
    intro i
    rw [disjoint_iff_inf_le]
    have hi :
        ((i : Submodule K[G] ρ.asModule) ⊓
            ⨆ (j : s) (_ : j ≠ i), (j : Submodule K[G] ρ.asModule)) ≤ ⊥ := by
      simpa [disjoint_iff_inf_le] using hs_indep' i
    simpa [Submodule.restrictScalars_inf, Submodule.restrictScalars_iSup] using
      (Submodule.restrictScalars_mono (S := K) (hst := hi))
  have hs_top' : (⨆ i : s, (i : Submodule K[G] ρ.asModule)) = ⊤ := by
    simpa [sSup_eq_iSup'] using hs_top
  have hσ_top :
      (⨆ i : s, Submodule.restrictScalars K (i : Submodule K[G] ρ.asModule)) = ⊤ := by
    simpa [Submodule.restrictScalars_iSup] using
      congrArg (Submodule.restrictScalars K) hs_top'
  simpa [toSubmodule_ofSubmodule'_eq_restrictScalars_support_local (ρ := ρ)] using
    (show
      iSupIndep (fun i : s ↦ Submodule.restrictScalars K (i : Submodule K[G] ρ.asModule)) ∧
        (⨆ i : s, Submodule.restrictScalars K (i : Submodule K[G] ρ.asModule)) = ⊤ from
      ⟨hσ_indep, hσ_top⟩)

/-- Helper for Exercise 12-12.2-6: the scalar extension of a finite-dimensional realizing model
admits a `Fin n`-indexed decomposition into irreducible subrepresentations over an arbitrary
target field. -/
theorem scalar_extension_character_eq_sum_irreducible_subcharacters_fin_local
    {K : Type v} [Field K]
    {L : Type*} [Field L] [CharZero L] [Algebra K L]
    (τ : Rep K G)
    [FiniteDimensional K τ] :
    ∃ (n : ℕ) (σ : Fin n → Subrepresentation (Representation.scalarExtension (k := L) τ.ρ)),
      (Representation.scalarExtension (k := L) τ.ρ).character =
        ∑ i, ((σ i).toRepresentation).character ∧
      ∀ i, (σ i).toRepresentation.IsIrreducible := by
  classical
  let ρL := Representation.scalarExtension (k := L) τ.ρ
  have hcard_ne : (Nat.card G : L) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  letI : NeZero (Nat.card G : L) := ⟨hcard_ne⟩
  obtain ⟨s, hs_fin, hs_indep, hs_top, hs_simple⟩ :=
    exists_finite_sSupIndep_simple_submodule_family (ρ := ρL)
  letI : Fintype s := hs_fin.fintype
  let σs : s → Subrepresentation ρL := fun i ↦ Subrepresentation.ofSubmodule' i.1
  have hσs :
      iSupIndep (fun i ↦ (σs i).toSubmodule) ∧
        (⨆ i, (σs i).toSubmodule) = ⊤ := by
    simpa [σs] using
      (iSupIndep_and_iSup_top_of_subtype_ofSubmodule'_family_support_local
        (ρ := ρL) (s := s) hs_indep hs_top)
  rcases hσs with ⟨hσs_indep, hσs_top⟩
  let e : Fin (Fintype.card s) ≃ s := (Fintype.equivFin s).symm
  let σ : Fin (Fintype.card s) → Subrepresentation ρL := fun i ↦ σs (e i)
  have hσ_indep : iSupIndep (fun i ↦ (σ i).toSubmodule) := by
    -- Reindex the independent family along the explicit `Fin` owner.
    simpa [σ, e] using hσs_indep.comp e.injective
  have hσ_top : (⨆ i, (σ i).toSubmodule) = ⊤ := by
    -- Reindex the spanning `iSup` along the same equivalence.
    calc
      (⨆ i, (σ i).toSubmodule) = ⨆ j : s, (σs j).toSubmodule := by
        simpa [σ, e] using (e.iSup_comp (g := fun j : s ↦ (σs j).toSubmodule))
      _ = ⊤ := hσs_top
  let hinternal : DirectSum.IsInternal (fun i ↦ (σ i).toSubmodule) :=
    DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top hσ_indep hσ_top
  refine ⟨Fintype.card s, σ, ?_, ?_⟩
  · -- First write the scalar extension character as the sum over the anonymous finite family,
    -- now directly over the concrete `Fin`-indexed owner.
    exact
      character_eq_sum_character_of_internal_decomposition_support_local
        (ρ := ρL) (σ := σ) hinternal
  · intro i
    -- Each finite owner summand comes from a simple `K[G]`-submodule, hence is irreducible.
    exact
      isIrreducible_toRepresentation_of_isSimpleModule_asSubmodule
        (ρ := ρL) (N := (e i).1) (hs_simple (e i).1 (e i).2)

/-- Helper for Exercise 12-12.2-6: the `Fin`-indexed scalar-extension decomposition also keeps
the internal direct-sum witness needed for multiplicity counting. -/
theorem scalar_extension_internal_irreducible_subrepresentations_fin_local
    {K : Type v} [Field K]
    {L : Type*} [Field L] [CharZero L] [Algebra K L]
    (τ : Rep K G)
    [FiniteDimensional K τ] :
    ∃ (n : ℕ) (σ : Fin n → Subrepresentation (Representation.scalarExtension (k := L) τ.ρ)),
      DirectSum.IsInternal (fun i ↦ (σ i).toSubmodule) ∧
      (Representation.scalarExtension (k := L) τ.ρ).character =
        ∑ i, ((σ i).toRepresentation).character ∧
      ∀ i, (σ i).toRepresentation.IsIrreducible := by
  classical
  let ρL := Representation.scalarExtension (k := L) τ.ρ
  have hcard_ne : (Nat.card G : L) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  letI : NeZero (Nat.card G : L) := ⟨hcard_ne⟩
  obtain ⟨s, hs_fin, hs_indep, hs_top, hs_simple⟩ :=
    exists_finite_sSupIndep_simple_submodule_family (ρ := ρL)
  letI : Fintype s := hs_fin.fintype
  let σs : s → Subrepresentation ρL := fun i ↦ Subrepresentation.ofSubmodule' i.1
  have hσs :
      iSupIndep (fun i ↦ (σs i).toSubmodule) ∧
        (⨆ i, (σs i).toSubmodule) = ⊤ := by
    simpa [σs] using
      (iSupIndep_and_iSup_top_of_subtype_ofSubmodule'_family_support_local
        (ρ := ρL) (s := s) hs_indep hs_top)
  rcases hσs with ⟨hσs_indep, hσs_top⟩
  let e : Fin (Fintype.card s) ≃ s := (Fintype.equivFin s).symm
  let σ : Fin (Fintype.card s) → Subrepresentation ρL := fun i ↦ σs (e i)
  have hσ_indep : iSupIndep (fun i ↦ (σ i).toSubmodule) := by
    -- Reindex the independent family along the explicit `Fin` owner.
    simpa [σ, e] using hσs_indep.comp e.injective
  have hσ_top : (⨆ i, (σ i).toSubmodule) = ⊤ := by
    -- Reindex the spanning `iSup` along the same equivalence.
    calc
      (⨆ i, (σ i).toSubmodule) = ⨆ j : s, (σs j).toSubmodule := by
        simpa [σ, e] using (e.iSup_comp (g := fun j : s ↦ (σs j).toSubmodule))
      _ = ⊤ := hσs_top
  let hinternal : DirectSum.IsInternal (fun i ↦ (σ i).toSubmodule) :=
    DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top hσ_indep hσ_top
  refine ⟨Fintype.card s, σ, hinternal, ?_, ?_⟩
  · -- The character formula now reuses the preserved internal direct-sum witness verbatim.
    exact
      character_eq_sum_character_of_internal_decomposition_support_local
        (ρ := ρL) (σ := σ) hinternal
  · intro i
    -- Each finite owner summand comes from a simple `K[G]`-submodule, hence is irreducible.
    exact
      isIrreducible_toRepresentation_of_isSimpleModule_asSubmodule
        (ρ := ρL) (N := (e i).1) (hs_simple (e i).1 (e i).2)

/-- Helper for Exercise 12-12.2-6: regrouping the visible scalar-extension decomposition by
isomorphism class yields the public packet with natural multiplicities, without any lifted-owner
transport. -/
theorem scalar_extension_public_packet_universe_local
    {K : Type v} [Field K] [CharZero K]
    (τ : Rep.{max u v} K G)
    [FiniteDimensional K τ] :
    ∃ (ι : Type) (_ : Fintype ι) (ψ : ι → Rep.{max u v} (AlgebraicClosure K) G) (d : ι → ℕ),
      (∀ i, 0 < d i) ∧
      (∀ i, FiniteDimensional (AlgebraicClosure K) (ψ i)) ∧
      PairwiseNonisomorphic ψ ∧
      (∀ i, (ψ i).ρ.IsIrreducible) ∧
      (Representation.scalarExtension (k := AlgebraicClosure K) τ.ρ).character =
        ∑ i, (d i : AlgebraicClosure K) • (ψ i).ρ.character := by
  classical
  obtain ⟨n, σ, _hinternal, hσchar, hσirr⟩ :=
    scalar_extension_internal_irreducible_subrepresentations_fin_local
      (G := G) (K := K) (L := AlgebraicClosure K) τ
  let r : Setoid (Fin n) :=
    { r := fun i j ↦ Nonempty (((σ i).toRepresentation).Equiv ((σ j).toRepresentation))
      iseqv :=
        ⟨fun i ↦ ⟨Representation.Equiv.refl _⟩,
          fun {i j} hij ↦ by
            rcases hij with ⟨e⟩
            exact ⟨e.symm⟩,
          fun {i j k} hij hjk ↦ by
            rcases hij with ⟨eij⟩
            rcases hjk with ⟨ejk⟩
            exact ⟨eij.trans ejk⟩⟩ }
  let ι := Quotient r
  letI : Finite ι := by
    refine Finite.of_surjective (fun i : Fin n ↦ (⟦i⟧ : Quotient r)) ?_
    intro q
    exact ⟨Quotient.out q, Quotient.out_eq q⟩
  letI : Fintype ι := Fintype.ofFinite ι
  let ψ : ι → Rep (AlgebraicClosure K) G :=
    fun q ↦ Rep.of ((σ (Quotient.out q)).toRepresentation)
  have hψ_fd : ∀ i, FiniteDimensional (AlgebraicClosure K) (ψ i) := by
    intro i
    letI : (ψ i).ρ.IsIrreducible := by
      simpa [ψ] using hσirr (Quotient.out i)
    exact Representation.IsIrreducible.finiteDimensional_of_finite (ρ := (ψ i).ρ)
  have hψ_pairwise : PairwiseNonisomorphic ψ := by
    intro q q' hqq' hIso
    have hclasses :
        (⟦Quotient.out q⟧ : ι) = ⟦Quotient.out q'⟧ := by
      apply Quotient.sound
      rcases hIso with ⟨e⟩
      exact ⟨Representation.equivOfIso e⟩
    apply hqq'
    calc
      q = (⟦Quotient.out q⟧ : ι) := (Quotient.out_eq q).symm
      _ = ⟦Quotient.out q'⟧ := hclasses
      _ = q' := Quotient.out_eq q'
  have hψ_irr : ∀ i, (ψ i).ρ.IsIrreducible := by
    intro i
    simpa [ψ] using hσirr (Quotient.out i)
  let S : ι → Finset (Fin n) :=
    fun i ↦ Finset.univ.filter fun j ↦
      Nonempty (((σ j).toRepresentation).Equiv (ψ i).ρ)
  let covered : Finset (Fin n) := Finset.univ.biUnion S
  let d : ι → ℕ := fun i ↦ (S i).card
  have hd_pos : ∀ i, 0 < d i := by
    intro i
    dsimp [d]
    refine Finset.card_pos.mpr ?_
    refine ⟨Quotient.out i, ?_⟩
    exact Finset.mem_filter.mpr ⟨by simp, by
      simpa [ψ] using
        (show Nonempty (((σ (Quotient.out i)).toRepresentation).Equiv
            ((σ (Quotient.out i)).toRepresentation)) from
          ⟨Representation.Equiv.refl _⟩)⟩
  have hS_disjoint : Pairwise fun i i' ↦ Disjoint (S i) (S i') := by
    intro i i' hii
    refine Finset.disjoint_left.mpr fun j hj hj' ↦ ?_
    rcases (Finset.mem_filter.mp hj).2 with ⟨e⟩
    rcases (Finset.mem_filter.mp hj').2 with ⟨e'⟩
    have hclasses :
        (⟦Quotient.out i⟧ : ι) = ⟦Quotient.out i'⟧ := by
      apply Quotient.sound
      exact ⟨e.symm.trans e'⟩
    apply hii
    calc
      i = (⟦Quotient.out i⟧ : ι) := (Quotient.out_eq i).symm
      _ = ⟦Quotient.out i'⟧ := hclasses
      _ = i' := Quotient.out_eq i'
  have hcovered_univ : covered = Finset.univ := by
    apply Finset.ext
    intro j
    constructor
    · intro _
      simp
    · intro hj
      refine Finset.mem_biUnion.mpr ?_
      refine ⟨(⟦j⟧ : ι), by simp, ?_⟩
      have hclass :
          Nonempty (((σ j).toRepresentation).Equiv
            ((σ (Quotient.out (⟦j⟧ : ι))).toRepresentation)) := by
        exact Quotient.exact (Quotient.out_eq (⟦j⟧ : ι)).symm
      exact Finset.mem_filter.mpr ⟨by simp, by simpa [ψ] using hclass⟩
  have hcovered_raw (g : G) :
      Finset.sum covered (fun j ↦ ((σ j).toRepresentation).character g) =
        ∑ i : ι, Finset.sum (S i) (fun j ↦ ((σ j).toRepresentation).character g) := by
    rw [show covered = Finset.univ.biUnion S from rfl]
    exact Finset.sum_biUnion fun i _ i' _ hii ↦ hS_disjoint hii
  refine ⟨ι, inferInstance, ψ, d, hd_pos, hψ_fd, hψ_pairwise, hψ_irr, ?_⟩
  -- Regroup the visible scalar-extension summands by isomorphism class before reading off the
  -- packet coefficients.
  ext g
  have hS_sum (i : ι) :
      Finset.sum (S i) (fun j ↦ ((σ j).toRepresentation).character g) =
        (d i : AlgebraicClosure K) * (ψ i).ρ.character g := by
    calc
      Finset.sum (S i) (fun j ↦ ((σ j).toRepresentation).character g) =
          Finset.sum (S i) (fun _j ↦ (ψ i).ρ.character g) := by
            refine Finset.sum_congr rfl fun j hj ↦ ?_
            rcases (Finset.mem_filter.mp hj).2 with ⟨e⟩
            simpa using congrArg (fun χ : G → AlgebraicClosure K ↦ χ g)
              (Representation.char_iso e)
      _ = (S i).card * (ψ i).ρ.character g := by
            simp
      _ = (d i : AlgebraicClosure K) * (ψ i).ρ.character g := by
            simp [d]
  calc
    (Representation.scalarExtension (k := AlgebraicClosure K) τ.ρ).character g
        = ∑ j : Fin n, ((σ j).toRepresentation).character g := by
            simpa using congrArg (fun χ : G → AlgebraicClosure K ↦ χ g) hσchar
    _ = Finset.sum covered (fun j ↦ ((σ j).toRepresentation).character g) := by
          simpa [covered, hcovered_univ]
    _ = ∑ i : ι, Finset.sum (S i) (fun j ↦ ((σ j).toRepresentation).character g) :=
          hcovered_raw g
    _ = ∑ i : ι, (d i : AlgebraicClosure K) * (ψ i).ρ.character g := by
          refine Finset.sum_congr rfl fun i _ ↦ hS_sum i
    _ = (∑ i, (d i : AlgebraicClosure K) • (ψ i).ρ.character) g := by
          simp [smul_eq_mul]

end ExtensionPart

end Exercise_12_12_2_6
end Representation
