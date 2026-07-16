import Mathlib
import LinearRepresentations_Serre_1977.Serre.Chap10.Definition_10_10_1_3
import LinearRepresentations_Serre_1977.Serre.Chap11.Remark_11_11_1_3.TensorCharacterRingRestriction
import LinearRepresentations_Serre_1977.Serre.Chap11.Remark_11_11_1_3.RestrictionFamily
import LinearRepresentations_Serre_1977.Serre.Chap11.Remark_11_11_1_3.ElementaryConjugation
import LinearRepresentations_Serre_1977.Serre.Chap11.Remark_11_11_1_3.ElementaryDetection
import LinearRepresentations_Serre_1977.Serre.Chap11.Remark_11_11_1_3.IntegralRestrictionSplitting
import LinearRepresentations_Serre_1977.Serre.Chap11.Remark_11_11_1_3.CokernelSplit
import LinearRepresentations_Serre_1977.Serre.Chap11.Remark_11_11_1_3.ElementaryCoherence
import LinearRepresentations_Serre_1977.Serre.Chap11.Remark_11_11_1_3.SubgroupLinearPairing
import LinearRepresentations_Serre_1977.Serre.Chap11.Remark_11_11_1_3.TopLocalPairing
import LinearRepresentations_Serre_1977.Serre.Chap11.Remark_11_11_1_3.CoatomDivisibility
import LinearRepresentations_Serre_1977.Serre.Chap11.Remark_11_11_1_3.KernelQuotientCharacters
import LinearRepresentations_Serre_1977.Serre.Chap11.Remark_11_11_1_3.CyclicQuotientPairings
import LinearRepresentations_Serre_1977.Serre.Chap11.Remark_11_11_1_3.QuotientPullbackPairings
import LinearRepresentations_Serre_1977.Serre.Chap11.Remark_11_11_1_3.QuotientPullbackDivisibility
import LinearRepresentations_Serre_1977.Serre.Chap11.Remark_11_11_1_3.StrictBranchResidual
import LinearRepresentations_Serre_1977.Serre.Chap11.Remark_11_11_1_3.MappedCoatomSlices
import LinearRepresentations_Serre_1977.Serre.Chap11.Remark_11_11_1_3.MappedCoatomReindexing
import LinearRepresentations_Serre_1977.Serre.Chap11.Remark_11_11_1_3.StrictKernelGrowth
import LinearRepresentations_Serre_1977.Serre.Chap11.Remark_11_11_1_3.ChosenCoatomFaithful
import LinearRepresentations_Serre_1977.Serre.Chap11.Remark_11_11_1_3.KernelQuotientRecursion
import LinearRepresentations_Serre_1977.Serre.Chap11.Remark_11_11_1_3.AmbientCoatomInduction
import LinearRepresentations_Serre_1977.Serre.Chap11.Remark_11_11_1_3.AmbientResidualFamily
import LinearRepresentations_Serre_1977.Serre.Chap11.Remark_11_11_1_3.ResidualIntegralityCriterion

noncomputable section

universe v

namespace Representation

section CharacterizationOfCharacters

open scoped Pointwise Representation SubgroupInduction TensorProduct

variable {G : Type} [Group G] [Finite G]
variable {A : Type v} [CommRing A]

local notation:max s " •ᶜ " H => (MulAut.conj s • H : Subgroup G)

/-- Helper for Remark 11-11.1-3: every subgroup of a finite group is finite. -/
local instance fintypeHelperLocalCoherenceDefectSaturation1 (H : Subgroup G) : Fintype H := Fintype.ofFinite H

/-- Helper for Remark 11-11.1-3: once a chosen restriction splitting removes the global part of a
family with defect `n • t`, the remaining task is to divide that residual family by `n` inside
the local product. -/
private theorem residual_family_divisible_of_multiple_coherence_defect
    (X : Finset (Subgroup G))
    (hXelem : ∀ H : Subgroup G, H ∈ X ↔ IsElementary H)
    (s : ((H : X) → R(H.1)) →ₗ[ℤ] R(G))
    (hs : Function.LeftInverse s (Representation.characterRingRestriction X).toLinearMap)
    {x : (H : X) → R(H.1)} {t : elementary_coherence_target X hXelem} {n : ℤ}
    (hn : n ≠ 0) (hx : s x = 0)
    (hdx : elementary_coherence_defect X hXelem x = n • t) :
    ∃ y : (H : X) → R(H.1), n • y = x := by
  classical
  let y : (H : X) → R(H.1) := fun H ↦
    ⟨fun h : H.1 ↦ ((x H : H.1 → ℂ) h) / (n : ℂ),
      scaled_residual_coordinate_mem_characterRing X hXelem s hs hn hx hdx H⟩
  refine ⟨y, ?_⟩
  have hnC : (n : ℂ) ≠ 0 := by
    exact_mod_cast hn
  ext H h
  -- The chosen coordinatewise division multiplies back to the original local character.
  have hcoe : ((n • y H : R(H.1)) : H.1 → ℂ) = (n : ℂ) • ((y H : R(H.1)) : H.1 → ℂ) := by
    ext z
    simp [zsmul_eq_mul]
  calc
    (((n • y) H : R(H.1)) : H.1 → ℂ) h = ((n • y H : R(H.1)) : H.1 → ℂ) h := by
      rw [Pi.smul_apply]
    _ = ((n : ℂ) • ((y H : R(H.1)) : H.1 → ℂ)) h := by rw [hcoe]
    _ = (n : ℂ) * (((x H : H.1 → ℂ) h) / (n : ℂ)) := rfl
    _ = ((x H : H.1 → ℂ) h) := by
      rw [mul_comm]
      exact div_mul_cancel₀ _ hnC

/-- Helper for Remark 11-11.1-3: nonzero integer multiples can be cancelled in the coherence
target by evaluating each coordinate in the corresponding complex character ring. -/
private theorem coherence_target_cancel_zsmul_by_evaluation
    (X : Finset (Subgroup G))
    (hXelem : ∀ H : Subgroup G, H ∈ X ↔ IsElementary H)
    {u v : elementary_coherence_target X hXelem} {n : ℤ} (hn : n ≠ 0)
    (h : n • u = n • v) :
    u = v := by
  apply Prod.ext
  · funext p
    -- Cancel the integer multiple on each restriction-defect coordinate separately.
    have hp := congrFun (congrArg Prod.fst h) p
    exact characterRing_zsmul_left_cancel (H := p.1.2.1) hn <| by
      simpa using hp
  · funext q
    -- The same evaluation argument works on each conjugation-defect coordinate.
    have hq := congrFun (congrArg Prod.snd h) q
    exact characterRing_zsmul_left_cancel (H := q.2 •ᶜ q.1.1) hn <| by
      simpa using hq

/-- Helper for Remark 11-11.1-3: if the integral coherence-defect image is saturated, then its
cokernel is torsion-free.
-/
private theorem elementary_coherence_defect_range_saturated
    (X : Finset (Subgroup G))
    (hXelem : ∀ H : Subgroup G, H ∈ X ↔ IsElementary H)
    {t : elementary_coherence_target X hXelem} {n : ℤ} (hn : n ≠ 0)
    (ht : n • t ∈ LinearMap.range (elementary_coherence_defect X hXelem)) :
    t ∈ LinearMap.range (elementary_coherence_defect X hXelem) := by
  -- Route correction: first normalize a preimage of `n • t` into the residual summand, then the
  -- only remaining work is to divide that residual family coordinatewise by `n`.
  obtain ⟨s, hs⟩ :=
    characterRingRestriction_has_leftInverse_of_detection_by_restrictions X <| by
      intro φ hφ
      exact
        Representation.classFunction_mem_characterRing_of_restrict_mem_on_elementarySubgroups
          X hXelem φ hφ
  obtain ⟨x, hx, hdx⟩ :=
    residual_family_of_multiple_coherence_defect X hXelem s hs ht
  obtain ⟨y, hy⟩ :=
    residual_family_divisible_of_multiple_coherence_defect X hXelem s
      (fun φ => hs φ)
      hn hx hdx
  refine ⟨y, ?_⟩
  -- Apply the defect map to `n • y = x` and cancel `n` in the defect target.
  have hny : n • elementary_coherence_defect X hXelem y = n • t := by
    calc
      n • elementary_coherence_defect X hXelem y = elementary_coherence_defect X hXelem x := by
        rw [← map_zsmul (elementary_coherence_defect X hXelem) n y, hy]
      _ = n • t := hdx
  exact coherence_target_cancel_zsmul_by_evaluation X hXelem hn hny

/-- Helper for Remark 11-11.1-3: saturation of the integral coherence-defect image makes the
coherence-defect cokernel torsion-free.
-/
private theorem elementary_coherence_defect_cokernel_torsion_free
    (X : Finset (Subgroup G))
    (hXelem : ∀ H : Subgroup G, H ∈ X ↔ IsElementary H) :
    Module.IsTorsionFree ℤ
      ((elementary_coherence_target X hXelem) ⧸
        LinearMap.range (elementary_coherence_defect X hXelem)) := by
  -- The saturated-image statement is exactly the torsion-free-cokernel bridge needed later.
  exact Representation.quotient_torsion_free_of_saturated_range
    (elementary_coherence_defect X hXelem)
    (elementary_coherence_defect_range_saturated X hXelem)

/-- Helper for Remark 11-11.1-3: once the integral coherence-defect cokernel is torsion-free, the
range inclusion splits over `ℤ`.
-/
private theorem elementary_coherence_defect_range_subtype_split
    (X : Finset (Subgroup G))
    (hXelem : ∀ H : Subgroup G, H ∈ X ↔ IsElementary H) :
    ∃ r : elementary_coherence_target X hXelem →ₗ[ℤ]
        LinearMap.range (elementary_coherence_defect X hXelem),
      Function.LeftInverse r
        ((LinearMap.range (elementary_coherence_defect X hXelem)).subtype) := by
  -- The retraction comes from the abstract saturated-splitting lemma; working over an opaque
  -- module keeps the unifier away from the concrete product's competing `Module ℤ` towers.
  letI : ∀ p : elementary_restriction_relation X, Module.Finite ℤ (R(p.1.2.1)) := fun p ↦
    show Module.Finite ℤ (R(p.1.2.1)) from characterRing_moduleFinite
  letI : ∀ q : elementary_conjugation_relation X, Module.Finite ℤ (R(q.2 •ᶜ q.1.1)) := fun q ↦
    show Module.Finite ℤ (R(q.2 •ᶜ q.1.1)) from characterRing_moduleFinite
  letI : Module.Finite ℤ (∀ p : elementary_restriction_relation X, R(p.1.2.1)) :=
    Module.Finite.pi
  letI : Module.Finite ℤ (∀ q : elementary_conjugation_relation X, R(q.2 •ᶜ q.1.1)) :=
    Module.Finite.pi
  letI : Module.Finite ℤ (elementary_coherence_target X hXelem) :=
    Module.Finite.prod
  exact
    Representation.exists_leftInverse_subtype_of_saturated
      (LinearMap.range (elementary_coherence_defect X hXelem))
      (fun hn ht => elementary_coherence_defect_range_saturated X hXelem hn ht)

/-- Helper for Remark 11-11.1-3: base change carries the integral coherence defect to the
base-changed range inclusion followed by the base-changed range-restricted defect. -/
private theorem coherence_defect_baseChange_eq_subtype_comp_rangeRestrict_baseChange
    (X : Finset (Subgroup G))
    (hXelem : ∀ H : Subgroup G, H ∈ X ↔ IsElementary H) :
    (elementary_coherence_defect X hXelem).baseChange A =
      ((((LinearMap.range (elementary_coherence_defect X hXelem)).subtype).baseChange A)).comp
        ((elementary_coherence_defect X hXelem).rangeRestrict.baseChange A) := by
  let d : ((H : X) → R(H.1)) →ₗ[ℤ] elementary_coherence_target X hXelem :=
    elementary_coherence_defect X hXelem
  let i : LinearMap.range d →ₗ[ℤ] elementary_coherence_target X hXelem :=
    (LinearMap.range d).subtype
  change d.baseChange A = (i.baseChange A).comp (d.rangeRestrict.baseChange A)
  apply TensorProduct.AlgebraTensorModule.ext
  intro a y
  -- On pure tensors, both sides apply `d` and then package the value into the actual range.
  simp [d, i]

/-- Helper for Remark 11-11.1-3: once the tensorized coherence defect vanishes, the
range-restricted tensor defect already vanishes. -/
theorem tensor_rangeRestrict_eq_zero_of_tensor_coherence_defect_eq_zero
    [Module.Flat ℤ A]
    (X : Finset (Subgroup G))
    (hXelem : ∀ H : Subgroup G, H ∈ X ↔ IsElementary H)
    {y : TensorProduct ℤ A ((H : X) → R(H.1))}
    (hy : (elementary_coherence_defect X hXelem).baseChange A y = 0) :
    ((elementary_coherence_defect X hXelem).rangeRestrict.baseChange A) y = 0 := by
  let d : ((H : X) → R(H.1)) →ₗ[ℤ] elementary_coherence_target X hXelem :=
    elementary_coherence_defect X hXelem
  let i : TensorProduct ℤ A (LinearMap.range d) →ₗ[A]
      TensorProduct ℤ A (elementary_coherence_target X hXelem) :=
    ((LinearMap.range d).subtype).baseChange A
  let drA : TensorProduct ℤ A ((H : X) → R(H.1)) →ₗ[A]
      TensorProduct ℤ A (LinearMap.range d) :=
    d.rangeRestrict.baseChange A
  have hfactor := congrArg
    (fun m :
      TensorProduct ℤ A ((H : X) → R(H.1)) →ₗ[A]
        TensorProduct ℤ A (elementary_coherence_target X hXelem) ↦ m y)
    (coherence_defect_baseChange_eq_subtype_comp_rangeRestrict_baseChange (A := A) X hXelem)
  have hi_zero : i (drA y) = (0 : TensorProduct ℤ A (elementary_coherence_target X hXelem)) := by
    -- Evaluate the factorization of `d.baseChange` at `y` and use the assumed vanishing.
    have hfactor' : d.baseChange A y = i (drA y) := by
      simpa [d, i, drA, LinearMap.comp_apply] using hfactor
    exact hfactor'.symm.trans hy
  have hi : Function.Injective i :=
    Representation.baseChange_injective_of_flat
      ((LinearMap.range d).subtype) (Submodule.injective_subtype _)
  -- Injectivity of the tensorized range inclusion removes the ambient target and leaves only the
  -- range-restricted defect.
  exact hi <| by
    calc
      i (drA y) = (0 : TensorProduct ℤ A (elementary_coherence_target X hXelem)) := hi_zero
      _ = i (0 : TensorProduct ℤ A (LinearMap.range d)) := by rw [LinearMap.map_zero]

/-- Helper for Remark 11-11.1-3: the integral local-family space splits as the product of the
global character ring and the range of the coherence-defect map. -/
private noncomputable def characterRingRestriction_split_with_coherence_defect
    (X : Finset (Subgroup G))
    (hXelem : ∀ H : Subgroup G, H ∈ X ↔ IsElementary H)
    (s : ((H : X) → R(H.1)) →ₗ[ℤ] R(G))
    (hs : Function.LeftInverse s (Representation.characterRingRestriction X).toLinearMap) :
    ((H : X) → R(H.1)) ≃ₗ[ℤ] R(G) ×
      LinearMap.range (elementary_coherence_defect X hXelem) := by
  let f : R(G) →ₗ[ℤ] ((H : X) → R(H.1)) := (Representation.characterRingRestriction X).toLinearMap
  let d : ((H : X) → R(H.1)) →ₗ[ℤ] elementary_coherence_target X hXelem :=
    elementary_coherence_defect X hXelem
  have hExact : Function.Exact f d.rangeRestrict := by
    let i : LinearMap.range d →ₗ[ℤ] elementary_coherence_target X hXelem :=
      (LinearMap.range d).subtype
    have hi : Function.Injective i := by
      intro x y hxy
      exact Subtype.ext hxy
    have hExact₀ : Function.Exact f d :=
      characterRingRestriction_exact_elementary_coherence_defect X hXelem
    -- Replace the defect codomain by its actual range so the splitting lemma can target a
    -- surjective second map.
    exact
      (Function.Injective.comp_exact_iff_exact
        (f := f) (g := d.rangeRestrict) (i := i) hi).mp <| by
        simpa [i] using hExact₀
  have hscomp : s.comp f = (LinearMap.id : R(G) →ₗ[ℤ] R(G)) := by
    apply LinearMap.ext
    intro χ
    exact hs χ
  -- Package the chosen retraction and the defect map into the standard split-exact equivalence.
  exact
    (Function.Exact.splitInjectiveEquiv
      (f := f) (g := d.rangeRestrict) hExact (LinearMap.surjective_rangeRestrict d)
      ⟨s, hscomp⟩).1

-- The final gluing theorem transports several tensor/product splittings across equivalences.


end CharacterizationOfCharacters

end Representation
