import Mathlib
import stacks_proof.stacks_project.Chap10.Definition_10_103_1

-- Declarations for this item will be appended below by the statement pipeline.

open IsLocalRing RingTheory Sequence
open scoped ENat

universe u v w

section

variable {R : Type u} {S : Type v} {N : Type w}
variable [CommRing R] [CommRing S] [Algebra R S]
variable [IsLocalRing R] [IsLocalRing S]
variable [IsNoetherianRing R] [IsNoetherianRing S]
variable [AddCommGroup N] [Module S N] [Module R N] [IsScalarTower R S N]

namespace Module

/-
Source/core/bridge triage:
* source-facing: `cohenMacaulay_iff_restrictScalars_of_surjective`, the textbook invariance of the
  Cohen-Macaulay condition under a surjective local map;
* core/canonical: the owner class `Module.CohenMacaulay`;
* bridge/view: `Module.CohenMacaulay.of_surjective`, the forward transport used when the owner
  instance over `S` is already available.

Primitive data are the surjective algebra map and the owner class itself. Finiteness over `R`
belongs to the derived API, obtained canonically from finiteness over `S` by restricting scalars,
rather than being packaged as separate primitive data in this file.
-/

/-- Helper for Lemma 10.103.6: mapping a regular sequence along `algebraMap R S` does not change
its regularity on `N`. -/
private theorem isRegular_map_algebraMap_iff (rs : List R) :
    IsRegular N (rs.map (algebraMap R S)) ↔ IsRegular N rs := by
  -- The additive identity on `N` intertwines the two scalar actions via `algebraMap`.
  exact
    (AddEquiv.refl N).isRegular_congr <|
      List.forall₂_map_left_iff.mpr <|
        List.forall₂_same.mpr fun r _ => algebraMap_smul S r

/-- Helper for Lemma 10.103.6: a list of elements of `maximalIdeal S` lifts to a list of elements
of `maximalIdeal R` with the same image under `algebraMap R S`. -/
private theorem exists_preimage_list_in_maximalIdeal
    (hsurj : Function.Surjective (algebraMap R S)) (rs : List S)
    (hI : Ideal.ofList rs ≤ maximalIdeal S) :
    ∃ rs' : List R,
      rs'.map (algebraMap R S) = rs ∧ Ideal.ofList rs' ≤ maximalIdeal R := by
  have hmap :
      Ideal.map (algebraMap R S) (maximalIdeal R) = maximalIdeal S :=
    IsLocalRing.map_maximalIdeal_of_surjective (algebraMap R S) hsurj
  induction rs with
  | nil =>
      have hnil : Ideal.ofList ([] : List R) ≤ maximalIdeal R := by
        simpa using (bot_le : (⊥ : Ideal R) ≤ maximalIdeal R)
      exact ⟨[], rfl, hnil⟩
  | cons s rs ih =>
      have hs_mem : s ∈ maximalIdeal S := by
        apply hI
        exact Ideal.subset_span (by simp)
      have hs_map : s ∈ Ideal.map (algebraMap R S) (maximalIdeal R) := by
        simpa [hmap] using hs_mem
      rcases (Ideal.mem_map_iff_of_surjective (f := algebraMap R S) hsurj).1 hs_map with
        ⟨r, hr, hrs⟩
      have htail_aux : Ideal.ofList rs ≤ Ideal.ofList (s :: rs) := by
        rw [Ideal.ofList_cons]
        exact le_sup_of_le_right le_rfl
      have htail : Ideal.ofList rs ≤ maximalIdeal S := by
        exact htail_aux.trans hI
      rcases ih htail with ⟨rs', hrs', hI'⟩
      have hr_le : Ideal.span ({r} : Set R) ≤ maximalIdeal R := by
        refine Ideal.span_le.mpr ?_
        intro x hx
        simp at hx
        simpa [hx] using hr
      have hcons : Ideal.ofList (r :: rs') ≤ maximalIdeal R := by
        rw [Ideal.ofList_cons]
        exact sup_le hr_le hI'
      exact ⟨r :: rs', by simp [hrs, hrs'], hcons⟩

/-- Helper for Lemma 10.103.6: the support dimension of `N` is unchanged after restricting scalars
along a surjective map `R → S`. -/
private theorem supportDim_eq_of_surjective
    (hsurj : Function.Surjective (algebraMap R S)) [Module.Finite R N] [Module.Finite S N] :
    Module.supportDim R N = Module.supportDim S N := by
  have hann :
      Ideal.comap (algebraMap R S) (Module.annihilator S N) = Module.annihilator R N :=
    Module.comap_annihilator (R₀ := R) (R := S) (M := N)
  have hann_le :
      Module.annihilator R N ≤ Ideal.comap (algebraMap R S) (Module.annihilator S N) :=
    hann.symm.le
  have hann_ge :
      Ideal.comap (algebraMap R S) (Module.annihilator S N) ≤ Module.annihilator R N :=
    hann.le
  let φ : R ⧸ Module.annihilator R N →+* S ⧸ Module.annihilator S N :=
    Ideal.quotientMap (Module.annihilator S N) (algebraMap R S) hann_le
  have hφinj : Function.Injective φ :=
    Ideal.quotientMap_injective' hann_ge
  have hφsurj : Function.Surjective φ :=
    Ideal.quotientMap_surjective hsurj
  have hφbij : Function.Bijective φ := ⟨hφinj, hφsurj⟩
  let e : R ⧸ Module.annihilator R N ≃+* S ⧸ Module.annihilator S N :=
    RingEquiv.ofBijective φ hφbij
  -- Compare both support dimensions through the quotient-annihilator presentation.
  rw [Module.supportDim_eq_ringKrullDim_quotient_annihilator,
    Module.supportDim_eq_ringKrullDim_quotient_annihilator,
    ringKrullDim_eq_of_ringEquiv e]

/-- Helper for Lemma 10.103.6: the lengths of regular sequences in the maximal ideals of `R` and
`S` coincide on `N` under a surjective local map `R → S`. -/
private theorem regularSequenceLengths_maximalIdeal_eq_of_surjective
    (hsurj : Function.Surjective (algebraMap R S)) :
    Ideal.regularSequenceLengths (maximalIdeal R) N =
      Ideal.regularSequenceLengths (maximalIdeal S) N := by
  have hmap :
      Ideal.map (algebraMap R S) (maximalIdeal R) = maximalIdeal S :=
    IsLocalRing.map_maximalIdeal_of_surjective (algebraMap R S) hsurj
  ext d
  constructor
  · rintro ⟨rs, hreg, hI, rfl⟩
    have hreg' : IsRegular N (rs.map (algebraMap R S)) :=
      (isRegular_map_algebraMap_iff (R := R) (S := S) (N := N) rs).2 hreg
    have hI' : Ideal.ofList (rs.map (algebraMap R S)) ≤ maximalIdeal S := by
      simpa [Ideal.map_ofList, hmap] using Ideal.map_mono (f := algebraMap R S) hI
    have hlen : (rs.length : ℕ∞) = (rs.map (algebraMap R S)).length := by
      simp
    exact ⟨rs.map (algebraMap R S), hreg', hI', hlen⟩
  · rintro ⟨rs, hreg, hI, rfl⟩
    rcases exists_preimage_list_in_maximalIdeal (R := R) (S := S) hsurj rs hI with
      ⟨rs', hrs', hI'⟩
    have hreg_map : IsRegular N (rs'.map (algebraMap R S)) := by
      simpa [hrs'] using hreg
    have hreg' : IsRegular N rs' :=
      (isRegular_map_algebraMap_iff (R := R) (S := S) (N := N) rs').1 hreg_map
    have hlen_nat : rs'.length = rs.length := by
      simpa using congrArg List.length hrs'
    have hlen : (rs'.length : ℕ∞) = rs.length :=
      congrArg (fun n : ℕ => (n : ℕ∞)) hlen_nat
    exact ⟨rs', hreg', hI', hlen.symm⟩

/-- Helper for Lemma 10.103.6: the module depth of `N` is unchanged after restricting scalars
along a surjective map `R → S`. -/
private theorem moduleDepth_eq_of_surjective
    (hsurj : Function.Surjective (algebraMap R S)) [Module.Finite R N] [Module.Finite S N] :
    moduleDepth R N = moduleDepth S N := by
  have hmap :
      Ideal.map (algebraMap R S) (maximalIdeal R) = maximalIdeal S :=
    IsLocalRing.map_maximalIdeal_of_surjective (algebraMap R S) hsurj
  have hsmul :
      (maximalIdeal S • (⊤ : Submodule S N)).restrictScalars R =
        maximalIdeal R • (⊤ : Submodule R N) := by
    simpa [hmap] using
      (Ideal.smul_restrictScalars (R := R) (S := S) (M := N) (maximalIdeal R)
        (⊤ : Submodule S N))
  have htop :
      maximalIdeal R • (⊤ : Submodule R N) = ⊤ ↔
        maximalIdeal S • (⊤ : Submodule S N) = ⊤ := by
    constructor
    · intro hR
      have hR' : (maximalIdeal S • (⊤ : Submodule S N)).restrictScalars R = ⊤ := by
        rw [hsmul, hR]
      exact
        (Submodule.restrictScalars_eq_top_iff (S := R)
          (p := maximalIdeal S • (⊤ : Submodule S N))).mp hR'
    · intro hS
      have hS' :
          (maximalIdeal S • (⊤ : Submodule S N)).restrictScalars R = ⊤ := by
        rw [hS, Submodule.restrictScalars_top]
      simpa [hsmul] using hS'
  by_cases hR : maximalIdeal R • (⊤ : Submodule R N) = ⊤
  · have hS : maximalIdeal S • (⊤ : Submodule S N) = ⊤ := htop.mp hR
    rw [show moduleDepth R N = ⊤ from Ideal.depth_eq_top_of_smul_top (maximalIdeal R) N hR,
      show moduleDepth S N = ⊤ from Ideal.depth_eq_top_of_smul_top (maximalIdeal S) N hS]
  · have hS : maximalIdeal S • (⊤ : Submodule S N) ≠ ⊤ := mt htop.mpr hR
    rw [show moduleDepth R N = sSup (Ideal.regularSequenceLengths (maximalIdeal R) N) from
        Ideal.depth_eq_sSup_lengths_of_smul_top_ne_top (maximalIdeal R) N hR,
      show moduleDepth S N = sSup (Ideal.regularSequenceLengths (maximalIdeal S) N) from
        Ideal.depth_eq_sSup_lengths_of_smul_top_ne_top (maximalIdeal S) N hS,
      regularSequenceLengths_maximalIdeal_eq_of_surjective (R := R) (S := S) (N := N) hsurj]

-- Proof sketch: identify `S` with a quotient of `R` using surjectivity of `algebraMap R S`.
-- Under restriction of scalars, the maximal ideal of `S` is the image of the maximal ideal of
-- `R`, and both the depth and the support dimension of `N` are unchanged by passage to this
-- quotient presentation. Therefore the defining equality for Cohen-Macaulay modules is equivalent
-- over `S` and over `R`.
/-- Lemma 10.103.6: for a surjective homomorphism `R → S` of Noetherian local rings and a finite
`S`-module `N`, the module `N` is Cohen-Macaulay over `S` if and only if it is
Cohen-Macaulay over `R` via restriction of scalars. -/
@[stacks 0AAD]
theorem cohenMacaulay_iff_restrictScalars_of_surjective
    (hsurj : Function.Surjective (algebraMap R S)) :
    CohenMacaulay S N ↔ CohenMacaulay R N := by
  constructor
  · intro hS
    let _ : CohenMacaulay S N := hS
    let _ : Module.Finite R S := Module.Finite.of_surjective (Algebra.linearMap R S) hsurj
    let _ : Module.Finite R N := Module.Finite.trans S N
    -- Transport the defining equality through the support-dimension and depth comparisons.
    have hdepthDim :
        Module.supportDim R N = WithBot.some (moduleDepth R N) := by
      rw [supportDim_eq_of_surjective (R := R) (S := S) (N := N) hsurj,
        moduleDepth_eq_of_surjective (R := R) (S := S) (N := N) hsurj,
        hS.supportDim_eq_moduleDepth]
    exact ⟨hdepthDim⟩
  · intro hR
    let _ : CohenMacaulay R N := hR
    let _ : Module.Finite S N := Module.Finite.of_restrictScalars_finite R S N
    -- The same invariance lemmas rewrite the `R`-equality back to the `S`-equality.
    have hdepthDim :
        Module.supportDim S N = WithBot.some (moduleDepth S N) := by
      rw [← supportDim_eq_of_surjective (R := R) (S := S) (N := N) hsurj,
        ← moduleDepth_eq_of_surjective (R := R) (S := S) (N := N) hsurj,
        hR.supportDim_eq_moduleDepth]
    exact ⟨hdepthDim⟩

namespace CohenMacaulay

/-- Restricting scalars along a surjective local ring map preserves the Cohen-Macaulay property. -/
theorem of_surjective (hsurj : Function.Surjective (algebraMap R S)) [CohenMacaulay S N] :
    CohenMacaulay R N :=
  (cohenMacaulay_iff_restrictScalars_of_surjective hsurj).1 ‹_›

end CohenMacaulay

end Module

end
