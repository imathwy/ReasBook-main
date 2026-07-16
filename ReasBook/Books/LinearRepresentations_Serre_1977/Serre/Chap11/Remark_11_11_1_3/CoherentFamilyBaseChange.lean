import Mathlib
import LinearRepresentations_Serre_1977.Serre.Chap10.Definition_10_10_1_3
import LinearRepresentations_Serre_1977.Serre.Chap11.Remark_11_11_1_3.TensorCharacterRingRestriction
import LinearRepresentations_Serre_1977.Serre.Chap11.Remark_11_11_1_3.RestrictionFamily
import LinearRepresentations_Serre_1977.Serre.Chap11.Remark_11_11_1_3.ElementaryConjugation
import LinearRepresentations_Serre_1977.Serre.Chap11.Remark_11_11_1_3.ElementaryDetection
import LinearRepresentations_Serre_1977.Serre.Chap11.Remark_11_11_1_3.IntegralRestrictionSplitting
import LinearRepresentations_Serre_1977.Serre.Chap11.Remark_11_11_1_3.ElementaryCoherence
import LinearRepresentations_Serre_1977.Serre.Chap11.Remark_11_11_1_3.CoherenceDefectSaturation

noncomputable section

universe v

namespace Representation

section CharacterizationOfCharacters

open scoped Pointwise Representation SubgroupInduction TensorProduct

variable {G : Type} [Group G] [Finite G]
variable {A : Type v} [CommRing A]

local notation:max s " •ᶜ " H => (MulAut.conj s • H : Subgroup G)

/-- Helper for Remark 11-11.1-3: every subgroup of a finite group is finite. -/
local instance fintypeHelperLocalCoherentFamilyBaseChange1 (H : Subgroup G) : Fintype H :=
  Fintype.ofFinite H

/-- Helper for Remark 11-11.1-3: for a coherent family of local tensor characters, the
base-changed integral coherence defect already vanishes on the transported family element.
This packages the equivalence-transport argument once, so the final gluing theorem only
consumes the vanishing statement. -/
theorem tensor_defect_baseChange_eq_zero_of_coherent_family
    (X : Finset (Subgroup G))
    (hXelem : ∀ H : Subgroup G, H ∈ X ↔ IsElementary H)
    (φX : (H : X) → A ⊗R(H.1))
    (hres :
      ∀ {H H' : X} (hH'H : H'.1 ≤ H.1),
        Subgroup.tensorCharacterRingRestrictionOfLe hH'H (φX H) = φX H')
    (hconj :
      ∀ (H : X) (s : G) (hHs : (s •ᶜ H.1) ∈ X),
        Subgroup.conjugateTensorCharacterRingTransport (A := A) H.1 s (φX H) =
          φX ⟨s •ᶜ H.1, hHs⟩) :
    (elementary_coherence_defect X hXelem).baseChange A
      ((tensorCharacterRingRestrictionFamilyEquiv (A := A) X).symm φX) = 0 := by
  classical
  let E := tensorCharacterRingRestrictionFamilyEquiv (A := A) X
  let C := tensorElementaryCoherenceEquiv (A := A) X hXelem
  let d : ((H : X) → R(H.1)) →ₗ[ℤ] elementary_coherence_target X hXelem :=
    elementary_coherence_defect X hXelem
  let dA := d.baseChange A
  let y := E.symm φX
  have hcoh :
      tensorElementaryCoherenceDefect (A := A) X hXelem φX =
        ((fun _ => 0), fun _ => 0) := by
    exact
      tensorElementaryCoherenceDefect_eq_zero_of_coherent_family
        (A := A) X hXelem φX hres hconj
  have hCA :
      tensorElementaryCoherenceDefect (A := A) X hXelem =
        (C.toLinearMap.comp dA).comp E.symm.toLinearMap := by
    exact tensorElementaryCoherenceDefect_eq_baseChange (A := A) X hXelem
  have hyCA :
      tensorElementaryCoherenceDefect (A := A) X hXelem φX = C (dA y) := by
    exact congrArg (fun m => m φX) hCA
  have hzero : dA y = 0 := by
    apply C.injective
    calc
      C (dA y) = tensorElementaryCoherenceDefect (A := A) X hXelem φX := hyCA.symm
      _ = ((fun _ => 0), fun _ => 0) := hcoh
      _ = C 0 := by
        change ((fun _ => 0), fun _ => 0) = ((fun _ => 0), fun _ => 0)
        rfl
  exact hzero

/-- Helper for Remark 11-11.1-3: base change transports the integral left-inverse property of a
chosen section of the restriction family map. -/
theorem tensor_section_comp_restriction_baseChange_eq_id
    (X : Finset (Subgroup G))
    (s : ((H : X) → R(H.1)) →ₗ[ℤ] R(G))
    (hs : Function.LeftInverse s (Representation.characterRingRestriction X).toLinearMap) :
    (s.baseChange A).comp
        ((Representation.characterRingRestriction X).toLinearMap.baseChange A) =
      (LinearMap.id : TensorProduct ℤ A (R(G)) →ₗ[A] TensorProduct ℤ A (R(G))) := by
  apply TensorProduct.AlgebraTensorModule.ext
  intro a y
  -- On pure tensors, the section property acts on the second factor only.
  simp only [LinearMap.comp_apply, LinearMap.baseChange_tmul, LinearMap.id_apply]
  exact congrArg (a ⊗ₜ[ℤ] ·) (hs y)

/-- Helper for Remark 11-11.1-3: base change transports the integral residual factorization of
the complementary projector through the coherence defect unchanged. -/
theorem tensor_residual_factorization_baseChange
    (X : Finset (Subgroup G))
    (hXelem : ∀ H : Subgroup G, H ∈ X ↔ IsElementary H)
    (s : ((H : X) → R(H.1)) →ₗ[ℤ] R(G))
    (q : LinearMap.range (elementary_coherence_defect X hXelem) →ₗ[ℤ] ((H : X) → R(H.1)))
    (hq : q.comp (elementary_coherence_defect X hXelem).rangeRestrict =
        (LinearMap.id : ((H : X) → R(H.1)) →ₗ[ℤ] ((H : X) → R(H.1))) -
          (Representation.characterRingRestriction X).toLinearMap.comp s) :
    (q.baseChange A).comp
        ((elementary_coherence_defect X hXelem).rangeRestrict.baseChange A) =
      (LinearMap.id :
          TensorProduct ℤ A ((H : X) → R(H.1)) →ₗ[A] TensorProduct ℤ A ((H : X) → R(H.1))) -
        ((Representation.characterRingRestriction X).toLinearMap.baseChange A).comp
          (s.baseChange A) := by
  apply TensorProduct.AlgebraTensorModule.ext
  intro a y
  have hy := congrArg (fun m => m y) hq
  simp only [LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.id_apply] at hy
  -- On pure tensors, the integral factorization acts on the second factor only.
  simp only [LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.id_apply,
    LinearMap.baseChange_tmul]
  rw [hy, TensorProduct.tmul_sub]

/-- Helper for Remark 11-11.1-3 (abstract form): if the complementary projector `id - f ∘ s`
factors through a defect map `dr` via `q`, then on any vector killed by `dr` the composite
`f ∘ s` acts as the identity. Stated over abstract modules so that no large tensor-product
instance search happens inside this proof. -/
theorem section_apply_eq_of_residual_factorization
    {R M N P : Type*} [CommRing R] [AddCommGroup M] [AddCommGroup N] [AddCommGroup P]
    [Module R M] [Module R N] [Module R P]
    (f : N →ₗ[R] M) (s : M →ₗ[R] N) (dr : M →ₗ[R] P) (q : P →ₗ[R] M)
    (hq : q.comp dr = (LinearMap.id : M →ₗ[R] M) - f.comp s)
    {y : M} (hy : dr y = 0) : f (s y) = y := by
  have h := congrArg (fun m : M →ₗ[R] M => m y) hq
  simp only [LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.id_apply, hy, map_zero] at h
  exact (sub_eq_zero.mp h.symm).symm

/-- Helper for Remark 11-11.1-3: the base-changed integral section, applied to the transport of a
coherent tensor family through the family equivalence, is fixed by the base-changed restriction
map. This is the residual-projector argument: the base-changed coherence defect kills the
transported family element, so the complementary projector vanishes on it. -/
theorem tensor_section_baseChange_fixes_coherent_family
    [Module.Flat ℤ A]
    (X : Finset (Subgroup G))
    (hXelem : ∀ H : Subgroup G, H ∈ X ↔ IsElementary H)
    (φX : (H : X) → A ⊗R(H.1))
    (hres :
      ∀ {H H' : X} (hH'H : H'.1 ≤ H.1),
        Subgroup.tensorCharacterRingRestrictionOfLe hH'H (φX H) = φX H')
    (hconj :
      ∀ (H : X) (s : G) (hHs : (s •ᶜ H.1) ∈ X),
        Subgroup.conjugateTensorCharacterRingTransport (A := A) H.1 s (φX H) =
          φX ⟨s •ᶜ H.1, hHs⟩)
    (s : ((H : X) → R(H.1)) →ₗ[ℤ] R(G))
    (q : LinearMap.range (elementary_coherence_defect X hXelem) →ₗ[ℤ] ((H : X) → R(H.1)))
    (hq : q.comp (elementary_coherence_defect X hXelem).rangeRestrict =
        (LinearMap.id : ((H : X) → R(H.1)) →ₗ[ℤ] ((H : X) → R(H.1))) -
          (Representation.characterRingRestriction X).toLinearMap.comp s) :
    ((Representation.characterRingRestriction X).toLinearMap.baseChange A)
        ((s.baseChange A) ((tensorCharacterRingRestrictionFamilyEquiv (A := A) X).symm φX)) =
      (tensorCharacterRingRestrictionFamilyEquiv (A := A) X).symm φX := by
  have hdA0 :=
    tensor_defect_baseChange_eq_zero_of_coherent_family (A := A) X hXelem φX hres hconj
  have hdrA0 :=
    tensor_rangeRestrict_eq_zero_of_tensor_coherence_defect_eq_zero (A := A) X hXelem hdA0
  have hqA := tensor_residual_factorization_baseChange (A := A) X hXelem s q hq
  exact section_apply_eq_of_residual_factorization _ _ _ _ hqA hdrA0

/-- Helper for Remark 11-11.1-3: applying the base-changed integral section after transporting a
coherent tensor family back through the family equivalence reproduces the family on every
elementary subgroup. This packages the residual-projector argument in one declaration. -/
theorem tensor_family_section_restricts_of_coherent_family
    [Module.Flat ℤ A]
    (X : Finset (Subgroup G))
    (hXelem : ∀ H : Subgroup G, H ∈ X ↔ IsElementary H)
    (φX : (H : X) → A ⊗R(H.1))
    (hres :
      ∀ {H H' : X} (hH'H : H'.1 ≤ H.1),
        Subgroup.tensorCharacterRingRestrictionOfLe hH'H (φX H) = φX H')
    (hconj :
      ∀ (H : X) (s : G) (hHs : (s •ᶜ H.1) ∈ X),
        Subgroup.conjugateTensorCharacterRingTransport (A := A) H.1 s (φX H) =
          φX ⟨s •ᶜ H.1, hHs⟩)
    (s : ((H : X) → R(H.1)) →ₗ[ℤ] R(G))
    (q : LinearMap.range (elementary_coherence_defect X hXelem) →ₗ[ℤ] ((H : X) → R(H.1)))
    (hq : q.comp (elementary_coherence_defect X hXelem).rangeRestrict =
        (LinearMap.id : ((H : X) → R(H.1)) →ₗ[ℤ] ((H : X) → R(H.1))) -
          (Representation.characterRingRestriction X).toLinearMap.comp s) :
    ∀ H : X,
      Subgroup.tensorCharacterRingRestriction (A := A) H.1
        ((s.baseChange A)
          ((tensorCharacterRingRestrictionFamilyEquiv (A := A) X).symm φX)) = φX H := by
  intro H
  have hsec :=
    tensor_section_baseChange_fixes_coherent_family (A := A) X hXelem φX hres hconj s q hq
  have hfix :=
    (congrArg (tensorCharacterRingRestrictionFamilyEquiv (A := A) X) hsec).trans
      ((tensorCharacterRingRestrictionFamilyEquiv (A := A) X).apply_symm_apply φX)
  have hb :=
    congrArg
      (fun m =>
        m ((s.baseChange A) ((tensorCharacterRingRestrictionFamilyEquiv (A := A) X).symm φX)) H)
      (tensor_characterRingRestriction_family_eq_baseChange (A := A) X)
  exact hb.trans (congrFun hfix H)

/-- Helper for Remark 11-11.1-3: two global tensor characters with the same restrictions to all
the subgroups in `X` coincide as soon as the integral restriction map admits a left inverse. -/
theorem tensor_global_eq_of_restrictions_eq
    (X : Finset (Subgroup G))
    (s : ((H : X) → R(H.1)) →ₗ[ℤ] R(G))
    (hs : Function.LeftInverse s (Representation.characterRingRestriction X).toLinearMap)
    {ψ ψ' : A ⊗R(G)}
    (h : ∀ H : X,
      Subgroup.tensorCharacterRingRestriction (A := A) H.1 ψ =
        Subgroup.tensorCharacterRingRestriction (A := A) H.1 ψ') :
    ψ = ψ' := by
  classical
  let f : R(G) →ₗ[ℤ] ((H : X) → R(H.1)) := (Representation.characterRingRestriction X).toLinearMap
  let E := tensorCharacterRingRestrictionFamilyEquiv (A := A) X
  let fA := f.baseChange A
  let sA := s.baseChange A
  have hsA :
      sA.comp fA =
        (LinearMap.id : TensorProduct ℤ A (R(G)) →ₗ[A] TensorProduct ℤ A (R(G))) := by
    exact tensor_section_comp_restriction_baseChange_eq_id (A := A) X s hs
  have hfamilyψ : E (fA ψ) = E (fA ψ') := by
    funext H
    have hb1 :=
      congrArg (fun m => m ψ H)
        (tensor_characterRingRestriction_family_eq_baseChange (A := A) X)
    have hb2 :=
      congrArg (fun m => m ψ' H)
        (tensor_characterRingRestriction_family_eq_baseChange (A := A) X)
    exact hb1.symm.trans ((h H).trans hb2)
  have hEqBase : fA ψ = fA ψ' := E.injective hfamilyψ
  have hψ1 : sA (fA ψ) = ψ := by
    simpa [LinearMap.comp_apply] using congrArg (fun m => m ψ) hsA
  have hψ2 : sA (fA ψ') = ψ' := by
    simpa [LinearMap.comp_apply] using congrArg (fun m => m ψ') hsA
  calc
    ψ = sA (fA ψ) := hψ1.symm
    _ = sA (fA ψ') := by rw [hEqBase]
    _ = ψ' := hψ2

/-- Helper for Remark 11-11.1-3: given an integral section of the restriction family map together
with a residual factorization of the complementary projector through the coherence defect, every
coherent tensor family on `X` comes from a unique global tensor character. This assembles the
existence witness and the uniqueness argument in one fresh-budget declaration, so the final
public theorem only has to produce the section and the factorization. -/
theorem existsUnique_tensor_global_of_coherent_family_section
    [Module.Flat ℤ A]
    (X : Finset (Subgroup G))
    (hXelem : ∀ H : Subgroup G, H ∈ X ↔ IsElementary H)
    (φX : (H : X) → A ⊗R(H.1))
    (hres :
      ∀ {H H' : X} (hH'H : H'.1 ≤ H.1),
        Subgroup.tensorCharacterRingRestrictionOfLe hH'H (φX H) = φX H')
    (hconj :
      ∀ (H : X) (s : G) (hHs : (s •ᶜ H.1) ∈ X),
        Subgroup.conjugateTensorCharacterRingTransport (A := A) H.1 s (φX H) =
          φX ⟨s •ᶜ H.1, hHs⟩)
    (s : ((H : X) → R(H.1)) →ₗ[ℤ] R(G))
    (hs : Function.LeftInverse s (Representation.characterRingRestriction X).toLinearMap)
    (q : LinearMap.range (elementary_coherence_defect X hXelem) →ₗ[ℤ] ((H : X) → R(H.1)))
    (hq : q.comp (elementary_coherence_defect X hXelem).rangeRestrict =
        (LinearMap.id : ((H : X) → R(H.1)) →ₗ[ℤ] ((H : X) → R(H.1))) -
          (Representation.characterRingRestriction X).toLinearMap.comp s) :
    ∃! φ : A ⊗R(G),
      ∀ H : X, Subgroup.tensorCharacterRingRestriction (A := A) H.1 φ = φX H := by
  have hfam :=
    tensor_family_section_restricts_of_coherent_family (A := A) X hXelem φX hres hconj s q hq
  refine
    ⟨(s.baseChange A) ((tensorCharacterRingRestrictionFamilyEquiv (A := A) X).symm φX), ?_, ?_⟩
  · intro H
    exact hfam H
  · intro ψ hψ
    exact
      tensor_global_eq_of_restrictions_eq (A := A) X s hs
        (fun H => (hψ H).trans (hfam H).symm)

end CharacterizationOfCharacters

end Representation
