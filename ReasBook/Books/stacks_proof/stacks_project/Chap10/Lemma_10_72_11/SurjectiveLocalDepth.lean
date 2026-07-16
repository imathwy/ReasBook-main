import Mathlib
import stacks_proof.stacks_project.Chap10.Definition_10_72_1
import stacks_proof.stacks_project.Chap10.Lemma_10_63_13
import stacks_proof.stacks_project.Chap10.Lemma_10_63_15
import stacks_proof.stacks_project.Chap10.Lemma_10_63_16
import stacks_proof.stacks_project.Chap10.Lemma_10_63_18
import stacks_proof.stacks_project.Chap10.Lemma_10_72_7

open IsLocalRing
open scoped ENat

/-- Helper for Lemma 10.72.11: mapping a regular sequence along an algebra map preserves
regularity on the restricted-scalar module. -/
theorem isRegular_map_algebraMap_iff_for_entry
    {A : Type*} {B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    {M : Type*} [AddCommGroup M] [Module B M] [Module A M] [IsScalarTower A B M]
    (rs : List A) :
    RingTheory.Sequence.IsRegular M (rs.map (algebraMap A B)) ↔
      RingTheory.Sequence.IsRegular M rs := by
  -- The identity map on `M` intertwines the two scalar actions through `algebraMap A B`.
  exact
    (AddEquiv.refl M).isRegular_congr <|
      List.forall₂_map_left_iff.mpr <|
        List.forall₂_same.mpr fun r _ => algebraMap_smul B r

/-- Helper for Lemma 10.72.11: under a surjective local map, a list in the target maximal ideal
lifts to a list in the source maximal ideal with the same image. -/
theorem exists_preimage_list_in_maximalIdeal_of_surjective_for_entry
    {A : Type*} {B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    [IsLocalRing A] [IsLocalRing B]
    (hsurj : Function.Surjective (algebraMap A B)) (rs : List B)
    (hI : Ideal.ofList rs ≤ maximalIdeal B) :
    ∃ rs' : List A,
      rs'.map (algebraMap A B) = rs ∧ Ideal.ofList rs' ≤ maximalIdeal A := by
  have hmap :
      Ideal.map (algebraMap A B) (maximalIdeal A) = maximalIdeal B :=
    IsLocalRing.map_maximalIdeal_of_surjective (algebraMap A B) hsurj
  induction rs with
  | nil =>
      -- The empty list already lies in the source maximal ideal.
      have hnil : Ideal.ofList ([] : List A) ≤ maximalIdeal A := by
        simpa using (bot_le : (⊥ : Ideal A) ≤ maximalIdeal A)
      exact ⟨[], rfl, hnil⟩
  | cons s rs ih =>
      -- Lift the head entry from the target maximal ideal, then recurse on the tail.
      have hs_mem : s ∈ maximalIdeal B := by
        exact hI (Ideal.subset_span (by simp))
      have hs_map : s ∈ Ideal.map (algebraMap A B) (maximalIdeal A) := by
        simpa [hmap] using hs_mem
      rcases (Ideal.mem_map_iff_of_surjective (f := algebraMap A B) hsurj).1 hs_map with
        ⟨r, hr, hrs⟩
      have htail_aux : Ideal.ofList rs ≤ Ideal.ofList (s :: rs) := by
        rw [Ideal.ofList_cons]
        exact le_sup_of_le_right le_rfl
      have htail : Ideal.ofList rs ≤ maximalIdeal B := htail_aux.trans hI
      rcases ih htail with ⟨rs', hrs', hI'⟩
      have hr_le : Ideal.span ({r} : Set A) ≤ maximalIdeal A := by
        refine Ideal.span_le.mpr ?_
        intro x hx
        simp at hx
        simpa [hx] using hr
      have hcons : Ideal.ofList (r :: rs') ≤ maximalIdeal A := by
        rw [Ideal.ofList_cons]
        exact sup_le hr_le hI'
      exact ⟨r :: rs', by simp [hrs, hrs'], hcons⟩

/-- Helper for Lemma 10.72.11: under a surjective local map, the regular-sequence lengths in the
two maximal ideals agree on the same module. -/
theorem regularSequenceLengths_maximalIdeal_eq_of_surjective_for_entry
    {A : Type*} {B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    [IsLocalRing A] [IsLocalRing B]
    {M : Type*} [AddCommGroup M] [Module B M] [Module A M] [IsScalarTower A B M]
    (hsurj : Function.Surjective (algebraMap A B)) :
    Ideal.regularSequenceLengths (maximalIdeal A) M =
      Ideal.regularSequenceLengths (maximalIdeal B) M := by
  have hmap :
      Ideal.map (algebraMap A B) (maximalIdeal A) = maximalIdeal B :=
    IsLocalRing.map_maximalIdeal_of_surjective (algebraMap A B) hsurj
  ext d
  constructor
  · rintro ⟨rs, hreg, hI, rfl⟩
    -- Push a source regular sequence into the target maximal ideal.
    have hreg' : RingTheory.Sequence.IsRegular M (rs.map (algebraMap A B)) :=
      (isRegular_map_algebraMap_iff_for_entry (A := A) (B := B) (M := M) rs).2 hreg
    have hI' : Ideal.ofList (rs.map (algebraMap A B)) ≤ maximalIdeal B := by
      simpa [Ideal.map_ofList, hmap] using Ideal.map_mono (f := algebraMap A B) hI
    exact ⟨rs.map (algebraMap A B), hreg', hI', by simp⟩
  · rintro ⟨rs, hreg, hI, rfl⟩
    -- Pull a target regular sequence back through the surjective map.
    rcases exists_preimage_list_in_maximalIdeal_of_surjective_for_entry
        (A := A) (B := B) hsurj rs hI with
      ⟨rs', hrs', hI'⟩
    have hreg_map : RingTheory.Sequence.IsRegular M (rs'.map (algebraMap A B)) := by
      simpa [hrs'] using hreg
    have hreg' : RingTheory.Sequence.IsRegular M rs' :=
      (isRegular_map_algebraMap_iff_for_entry (A := A) (B := B) (M := M) rs').1 hreg_map
    have hlen_nat : rs'.length = rs.length := by
      simpa using congrArg List.length hrs'
    exact ⟨rs', hreg', hI', by exact_mod_cast hlen_nat.symm⟩

/-- Helper for Lemma 10.72.11: restricting scalars along a surjective local map does not change
module depth. -/
theorem moduleDepth_eq_of_surjective_for_entry
    {A : Type*} {B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    [IsLocalRing A] [IsLocalRing B] [IsNoetherianRing A] [IsNoetherianRing B]
    {M : Type*} [AddCommGroup M] [Module B M] [Module A M] [IsScalarTower A B M]
    [Module.Finite A M] [Module.Finite B M]
    (hsurj : Function.Surjective (algebraMap A B)) :
    moduleDepth A M = moduleDepth B M := by
  have hmap :
      Ideal.map (algebraMap A B) (maximalIdeal A) = maximalIdeal B :=
    IsLocalRing.map_maximalIdeal_of_surjective (algebraMap A B) hsurj
  have hsmul :
      (maximalIdeal B • (⊤ : Submodule B M)).restrictScalars A =
        maximalIdeal A • (⊤ : Submodule A M) := by
    -- The target maximal ideal is the image of the source maximal ideal under the surjective map.
    simpa [hmap] using
      (Ideal.smul_restrictScalars (R := A) (S := B) (M := M) (maximalIdeal A)
        (⊤ : Submodule B M))
  have htop :
      maximalIdeal A • (⊤ : Submodule A M) = ⊤ ↔
        maximalIdeal B • (⊤ : Submodule B M) = ⊤ := by
    constructor
    · intro hA
      have hA' : (maximalIdeal B • (⊤ : Submodule B M)).restrictScalars A = ⊤ := by
        rw [hsmul, hA]
      exact
        (Submodule.restrictScalars_eq_top_iff (S := A)
          (p := maximalIdeal B • (⊤ : Submodule B M))).mp hA'
    · intro hB
      have hB' :
          (maximalIdeal B • (⊤ : Submodule B M)).restrictScalars A = ⊤ := by
        rw [hB, Submodule.restrictScalars_top]
      simpa [hsmul] using hB'
  by_cases hA : maximalIdeal A • (⊤ : Submodule A M) = ⊤
  · -- In the `⊤` branch, both depths are infinite.
    rw [show moduleDepth A M = ⊤ from Ideal.depth_eq_top_of_smul_top (maximalIdeal A) M hA,
      show moduleDepth B M = ⊤ from Ideal.depth_eq_top_of_smul_top (maximalIdeal B) M (htop.mp hA)]
  · -- Otherwise, both depths are the supremum of regular-sequence lengths, which agree.
    have hB : maximalIdeal B • (⊤ : Submodule B M) ≠ ⊤ := mt htop.mpr hA
    rw [show moduleDepth A M = sSup (Ideal.regularSequenceLengths (maximalIdeal A) M) from
          Ideal.depth_eq_sSup_lengths_of_smul_top_ne_top (maximalIdeal A) M hA,
      show moduleDepth B M = sSup (Ideal.regularSequenceLengths (maximalIdeal B) M) from
          Ideal.depth_eq_sSup_lengths_of_smul_top_ne_top (maximalIdeal B) M hB,
      regularSequenceLengths_maximalIdeal_eq_of_surjective_for_entry
        (A := A) (B := B) (M := M) hsurj]
