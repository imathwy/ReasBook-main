import Mathlib
import StacksProject_2024.Chap10.Definition_10_72_1
import StacksProject_2024.Chap10.Definition_10_109_10
import StacksProject_2024.Chap10.Definition_10_157_1
import StacksProject_2024.Chap10.Lemma_10_72_5
import StacksProject_2024.Chap10.Lemma_10_104_9
import StacksProject_2024.Chap10.Lemma_10_106_3
import StacksProject_2024.Chap10.Lemma_10_106_6
import StacksProject_2024.Chap10.Lemma_10_107_14
import StacksProject_2024.Chap10.Lemma_10_109_6
import StacksProject_2024.Chap10.Lemma_10_109_7
import StacksProject_2024.Chap10.Lemma_10_109_12

universe u v w

open CategoryTheory ChainComplex
open scoped ENat

section

/-- Helper for Proposition 10.110.1: restricting scalars along a surjective local algebra map
does not change module depth. -/
lemma isRegular_map_algebraMap_iff_public
    {A : Type*} {B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    {N : Type*} [AddCommGroup N] [Module B N] [Module A N] [IsScalarTower A B N]
    (rs : List A) :
    RingTheory.Sequence.IsRegular N (rs.map (algebraMap A B)) ↔
      RingTheory.Sequence.IsRegular N rs := by
  -- The additive identity on `N` intertwines the two scalar actions via `algebraMap A B`.
  exact
    (AddEquiv.refl N).isRegular_congr <|
      List.forall₂_map_left_iff.mpr <|
        List.forall₂_same.mpr fun r _ => algebraMap_smul B r

/-- Helper for Proposition 10.110.1: under a surjective local algebra map, a list inside the
target maximal ideal lifts to a list in the source maximal ideal with the same image. -/
lemma exists_preimage_list_in_maximalIdeal_of_surjective_public
    {A : Type*} {B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    [IsLocalRing A] [IsLocalRing B]
    (hsurj : Function.Surjective (algebraMap A B)) (rs : List B)
    (hI : Ideal.ofList rs ≤ IsLocalRing.maximalIdeal B) :
    ∃ rs' : List A,
      rs'.map (algebraMap A B) = rs ∧ Ideal.ofList rs' ≤ IsLocalRing.maximalIdeal A := by
  have hmap :
      Ideal.map (algebraMap A B) (IsLocalRing.maximalIdeal A) = IsLocalRing.maximalIdeal B :=
    IsLocalRing.map_maximalIdeal_of_surjective (algebraMap A B) hsurj
  induction rs with
  | nil =>
      -- The empty list already lies in the source maximal ideal.
      have hnil : Ideal.ofList ([] : List A) ≤ IsLocalRing.maximalIdeal A := by
        simpa using (bot_le : (⊥ : Ideal A) ≤ IsLocalRing.maximalIdeal A)
      exact ⟨[], rfl, hnil⟩
  | cons s rs ih =>
      -- Lift the head entry from the target maximal ideal, then recurse on the tail.
      have hs_mem : s ∈ IsLocalRing.maximalIdeal B := by
        apply hI
        exact Ideal.subset_span (by simp)
      have hs_map : s ∈ Ideal.map (algebraMap A B) (IsLocalRing.maximalIdeal A) := by
        simpa [hmap] using hs_mem
      rcases (Ideal.mem_map_iff_of_surjective (f := algebraMap A B) hsurj).1 hs_map with
        ⟨r, hr, hrs⟩
      have htail_aux : Ideal.ofList rs ≤ Ideal.ofList (s :: rs) := by
        rw [Ideal.ofList_cons]
        exact le_sup_of_le_right le_rfl
      have htail : Ideal.ofList rs ≤ IsLocalRing.maximalIdeal B := htail_aux.trans hI
      rcases ih htail with ⟨rs', hrs', hI'⟩
      have hr_le : Ideal.span ({r} : Set A) ≤ IsLocalRing.maximalIdeal A := by
        refine Ideal.span_le.mpr ?_
        intro x hx
        simp at hx
        simpa [hx] using hr
      have hcons : Ideal.ofList (r :: rs') ≤ IsLocalRing.maximalIdeal A := by
        rw [Ideal.ofList_cons]
        exact sup_le hr_le hI'
      exact ⟨r :: rs', by simp [hrs, hrs'], hcons⟩

/-- Helper for Proposition 10.110.1: under a surjective local algebra map, regular-sequence
lengths in the two maximal ideals agree on the same restricted-scalar module. -/
lemma regularSequenceLengths_maximalIdeal_eq_of_surjective_public
    {A : Type*} {B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    [IsLocalRing A] [IsLocalRing B]
    {N : Type*} [AddCommGroup N] [Module B N] [Module A N] [IsScalarTower A B N]
    (hsurj : Function.Surjective (algebraMap A B)) :
    Ideal.regularSequenceLengths (IsLocalRing.maximalIdeal A) N =
      Ideal.regularSequenceLengths (IsLocalRing.maximalIdeal B) N := by
  have hmap :
      Ideal.map (algebraMap A B) (IsLocalRing.maximalIdeal A) = IsLocalRing.maximalIdeal B :=
    IsLocalRing.map_maximalIdeal_of_surjective (algebraMap A B) hsurj
  ext d
  constructor
  · rintro ⟨rs, hreg, hI, rfl⟩
    -- Push a source regular sequence into the target maximal ideal.
    have hreg' : RingTheory.Sequence.IsRegular N (rs.map (algebraMap A B)) :=
      (isRegular_map_algebraMap_iff_public (A := A) (B := B) (N := N) rs).2 hreg
    have hI' : Ideal.ofList (rs.map (algebraMap A B)) ≤ IsLocalRing.maximalIdeal B := by
      simpa [Ideal.map_ofList, hmap] using Ideal.map_mono (f := algebraMap A B) hI
    exact ⟨rs.map (algebraMap A B), hreg', hI', by simp⟩
  · rintro ⟨rs, hreg, hI, rfl⟩
    -- Pull a target regular sequence back through the surjective map.
    rcases exists_preimage_list_in_maximalIdeal_of_surjective_public
        (A := A) (B := B) hsurj rs hI with
      ⟨rs', hrs', hI'⟩
    have hreg_map : RingTheory.Sequence.IsRegular N (rs'.map (algebraMap A B)) := by
      simpa [hrs'] using hreg
    have hreg' : RingTheory.Sequence.IsRegular N rs' :=
      (isRegular_map_algebraMap_iff_public (A := A) (B := B) (N := N) rs').1 hreg_map
    have hlen_nat : rs'.length = rs.length := by
      simpa using congrArg List.length hrs'
    exact ⟨rs', hreg', hI', by exact_mod_cast hlen_nat.symm⟩

/-- Helper for Proposition 10.110.1: restricting scalars along a surjective local algebra map
does not change module depth. -/
lemma moduleDepth_eq_of_surjective_local_algebra
    {A : Type*} {B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    [IsLocalRing A] [IsLocalRing B] [IsNoetherianRing A] [IsNoetherianRing B]
    {N : Type*} [AddCommGroup N] [Module B N] [Module A N] [IsScalarTower A B N]
    [Module.Finite A N] [Module.Finite B N]
    (hsurj : Function.Surjective (algebraMap A B)) :
    moduleDepth A N = moduleDepth B N := by
  have hmap :
      Ideal.map (algebraMap A B) (IsLocalRing.maximalIdeal A) = IsLocalRing.maximalIdeal B :=
    IsLocalRing.map_maximalIdeal_of_surjective (algebraMap A B) hsurj
  have hsmul :
      (IsLocalRing.maximalIdeal B • (⊤ : Submodule B N)).restrictScalars A =
        IsLocalRing.maximalIdeal A • (⊤ : Submodule A N) := by
    -- The target maximal ideal is the image of the source maximal ideal under the surjective map.
    simpa [hmap] using
      (Ideal.smul_restrictScalars (R := A) (S := B) (M := N) (IsLocalRing.maximalIdeal A)
        (⊤ : Submodule B N))
  have htop :
      IsLocalRing.maximalIdeal A • (⊤ : Submodule A N) = ⊤ ↔
        IsLocalRing.maximalIdeal B • (⊤ : Submodule B N) = ⊤ := by
    constructor
    · intro hA
      have hA' :
          (IsLocalRing.maximalIdeal B • (⊤ : Submodule B N)).restrictScalars A = ⊤ := by
        rw [hsmul, hA]
      exact
        (Submodule.restrictScalars_eq_top_iff (S := A)
          (p := IsLocalRing.maximalIdeal B • (⊤ : Submodule B N))).mp hA'
    · intro hB
      have hB' :
          (IsLocalRing.maximalIdeal B • (⊤ : Submodule B N)).restrictScalars A = ⊤ := by
        rw [hB, Submodule.restrictScalars_top]
      simpa [hsmul] using hB'
  by_cases hA : IsLocalRing.maximalIdeal A • (⊤ : Submodule A N) = ⊤
  · -- In the `⊤` branch, both depths are infinite.
    rw [show moduleDepth A N = ⊤ from
          Ideal.depth_eq_top_of_smul_top (IsLocalRing.maximalIdeal A) N hA,
      show moduleDepth B N = ⊤ from
          Ideal.depth_eq_top_of_smul_top (IsLocalRing.maximalIdeal B) N (htop.mp hA)]
  · -- Otherwise both depths are the supremum of the same regular-sequence lengths.
    have hB : IsLocalRing.maximalIdeal B • (⊤ : Submodule B N) ≠ ⊤ := mt htop.mpr hA
    rw [show moduleDepth A N =
          sSup (Ideal.regularSequenceLengths (IsLocalRing.maximalIdeal A) N) from
          Ideal.depth_eq_sSup_lengths_of_smul_top_ne_top (IsLocalRing.maximalIdeal A) N hA,
      show moduleDepth B N =
          sSup (Ideal.regularSequenceLengths (IsLocalRing.maximalIdeal B) N) from
          Ideal.depth_eq_sSup_lengths_of_smul_top_ne_top (IsLocalRing.maximalIdeal B) N hB,
      regularSequenceLengths_maximalIdeal_eq_of_surjective_public
        (A := A) (B := B) (N := N) hsurj]

end
