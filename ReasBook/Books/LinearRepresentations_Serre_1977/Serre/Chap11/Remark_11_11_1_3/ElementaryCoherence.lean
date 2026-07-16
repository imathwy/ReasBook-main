import Mathlib
import LinearRepresentations_Serre_1977.Serre.Chap10.Definition_10_10_1_3
import LinearRepresentations_Serre_1977.Serre.Chap11.Remark_11_11_1_3.TensorCharacterRingRestriction
import LinearRepresentations_Serre_1977.Serre.Chap11.Remark_11_11_1_3.RestrictionFamily
import LinearRepresentations_Serre_1977.Serre.Chap11.Remark_11_11_1_3.ElementaryConjugation
import LinearRepresentations_Serre_1977.Serre.Chap11.Remark_11_11_1_3.ElementaryDetection
import LinearRepresentations_Serre_1977.Serre.Chap11.Remark_11_11_1_3.IntegralRestrictionSplitting

noncomputable section

universe v

namespace Representation

section CharacterizationOfCharacters

open scoped Pointwise Representation SubgroupInduction TensorProduct

variable {G : Type} [Group G] [Finite G]
variable {A : Type v} [CommRing A]

local notation:max s " •ᶜ " H => (MulAut.conj s • H : Subgroup G)

/-- Helper for Remark 11-11.1-3: every subgroup of a finite group is finite. -/
local instance elementaryCoherenceSubgroupFintypeLocal (H : Subgroup G) : Fintype H :=
  Fintype.ofFinite H
/-- Helper for Remark 11-11.1-3: inclusion relations among the elementary-indexed local
character-ring coordinates. -/
abbrev elementary_restriction_relation (X : Finset (Subgroup G)) :=
  { p : X × X // p.2.1 ≤ p.1.1 }

/-- Helper for Remark 11-11.1-3: conjugation relations among the elementary-indexed local
character-ring coordinates. -/
abbrev elementary_conjugation_relation (X : Finset (Subgroup G)) :=
  X × G

/-- Helper for Remark 11-11.1-3: the codomain collecting all restriction and conjugation defects
for an integral family on the elementary subgroups. -/
abbrev elementary_coherence_target
    (X : Finset (Subgroup G))
    (_hXelem : ∀ H : Subgroup G, H ∈ X ↔ IsElementary H) :=
  (∀ p : elementary_restriction_relation X, R(p.1.2.1)) ×
    (∀ q : elementary_conjugation_relation X, R(q.2 •ᶜ q.1.1))

/-- Helper for Remark 11-11.1-3: transporting the global restriction of a character along
conjugation agrees with restricting the same global character to the conjugate subgroup. -/
theorem characterRingTransport_global_restriction_eq_conjugate
    (H : Subgroup G) (s : G) (χ : R(G)) :
    Subgroup.characterRingTransport ((MulAut.conj s).subgroupMap H).symm ((H ↾R[ℂ]) χ) =
      ((s •ᶜ H) ↾R[ℂ]) χ := by
  apply Subtype.ext
  ext x
  change (χ : G → ℂ) (s⁻¹ * (x : G) * s) = (χ : G → ℂ) x
  exact (isClassFunction_of_mem_characterRingOverField (χ : G → ℂ) χ.property).eq_of_isConj <|
    isConj_iff.2 ⟨s, by group⟩

/-- Helper for Remark 11-11.1-3: the integral linear map whose vanishing encodes the restriction
and conjugation coherence conditions on a family of local characters indexed by elementary
subgroups. -/
def elementary_coherence_defect
    (X : Finset (Subgroup G))
    (hXelem : ∀ H : Subgroup G, H ∈ X ↔ IsElementary H) :
    ((H : X) → R(H.1)) →ₗ[ℤ] elementary_coherence_target X hXelem :=
  let restrictionDefect :
      ((H : X) → R(H.1)) →ₗ[ℤ] ∀ p : elementary_restriction_relation X, R(p.1.2.1) :=
    LinearMap.pi fun p =>
      let projH : ((H : X) → R(H.1)) →ₗ[ℤ] R(p.1.1.1) :=
        LinearMap.proj (R := ℤ) (φ := fun H : X ↦ R(H.1)) p.1.1
      let projH' : ((H : X) → R(H.1)) →ₗ[ℤ] R(p.1.2.1) :=
        LinearMap.proj (R := ℤ) (φ := fun H : X ↦ R(H.1)) p.1.2
      ((Subgroup.characterRingRestrictionOfLe p.2).toLinearMap.comp projH) - projH'
  let conjugationDefect :
      ((H : X) → R(H.1)) →ₗ[ℤ] ∀ q : elementary_conjugation_relation X, R(q.2 •ᶜ q.1.1) :=
    LinearMap.pi fun q =>
      let qH : X := ⟨q.2 •ᶜ q.1.1, elementary_mem_of_conj X hXelem q.1.2 q.2⟩
      let projH : ((H : X) → R(H.1)) →ₗ[ℤ] R(q.1.1) :=
        LinearMap.proj (R := ℤ) (φ := fun H : X ↦ R(H.1)) q.1
      (((Subgroup.characterRingTransport ((MulAut.conj q.2).subgroupMap q.1.1).symm :
            R(q.1.1) →ₐ[ℤ] R(q.2 •ᶜ q.1.1)).toLinearMap).comp projH) -
        LinearMap.proj qH
  LinearMap.prod restrictionDefect conjugationDefect

/-- Helper for Remark 11-11.1-3: the integral restriction family map is exact with the coherence
defect map, so the only obstruction to gluing a family in `Π_{H ∈ X} R(H)` is the vanishing of its
restriction and conjugation defects. -/
theorem characterRingRestriction_exact_elementary_coherence_defect
    (X : Finset (Subgroup G))
    (hXelem : ∀ H : Subgroup G, H ∈ X ↔ IsElementary H) :
    Function.Exact (Representation.characterRingRestriction X).toLinearMap
      (elementary_coherence_defect X hXelem) := by
  let f : R(G) →ₗ[ℤ] ((H : X) → R(H.1)) := (Representation.characterRingRestriction X).toLinearMap
  let d : ((H : X) → R(H.1)) →ₗ[ℤ] elementary_coherence_target X hXelem :=
    elementary_coherence_defect X hXelem
  refine LinearMap.exact_of_comp_eq_zero_of_ker_le_range ?_ ?_
  · -- Every global character family has zero restriction and conjugation defect.
    refine LinearMap.ext fun χ ↦ ?_
    ext x y
    · simp [elementary_coherence_defect, Representation.characterRingRestriction_apply,
        Subgroup.characterRingRestrictionOfLe_apply]
    · have hq := congrFun
        (show
          (((Subgroup.characterRingTransport ((MulAut.conj x.2).subgroupMap x.1.1).symm)
              ((x.1.1 ↾R[ℂ]) χ) : R(x.2 •ᶜ x.1.1)) : (x.2 •ᶜ x.1.1) → ℂ) =
            ((((x.2 •ᶜ x.1.1) ↾R[ℂ]) χ : R(x.2 •ᶜ x.1.1)) : (x.2 •ᶜ x.1.1) → ℂ) from
          congrArg
            (fun η : R(x.2 •ᶜ x.1.1) ↦ ((η : (x.2 •ᶜ x.1.1) → ℂ)))
            (characterRingTransport_global_restriction_eq_conjugate x.1.1 x.2 χ))
      simpa [d, f, elementary_coherence_defect, Representation.characterRingRestriction_apply,
        Subgroup.characterRingTransport_apply] using sub_eq_zero.mpr (hq y)
  · intro ψ hψ
    rw [LinearMap.mem_ker] at hψ
    have hres :
        ∀ {H H' : X} (hH'H : H'.1 ≤ H.1),
          ((hH'H ↾R[ℂ]) (ψ H) : R(H'.1)) = ψ H' := by
      intro H H' hH'H
      let p : elementary_restriction_relation X := ⟨(H, H'), hH'H⟩
      have hp : ((elementary_coherence_defect X hXelem ψ).1 p : R(H'.1)) = 0 := by
        exact congrFun (congrArg Prod.fst hψ) p
      -- The first defect block records exactly the restriction-compatibility equations.
      simpa [elementary_coherence_defect, p] using sub_eq_zero.mp hp
    have hconj :
        ∀ (H : X) (s : G) (hHs : (s •ᶜ H.1) ∈ X),
          Subgroup.characterRingTransport ((MulAut.conj s).subgroupMap H.1).symm (ψ H) =
            ψ ⟨s •ᶜ H.1, hHs⟩ := by
      intro H s hHs
      let Hs₀ : X := ⟨s •ᶜ H.1, elementary_mem_of_conj X hXelem H.2 s⟩
      have hHs₀ : Hs₀ = ⟨s •ᶜ H.1, hHs⟩ := by
        apply Subtype.ext
        rfl
      have hq : ((elementary_coherence_defect X hXelem ψ).2 (H, s) : R(s •ᶜ H.1)) = 0 := by
        exact congrFun (congrArg Prod.snd hψ) (H, s)
      -- The second defect block is the conjugation-compatibility condition.
      simpa [elementary_coherence_defect, Hs₀, hHs₀] using sub_eq_zero.mp hq
    obtain ⟨φ, hφ⟩ :=
      Representation.exists_glued_classFunction_of_coherent_character_family_on_elementarySubgroups
        X hXelem ψ hres hconj
    have hφ_mem : (φ : G → ℂ) ∈ R(G) := by
      -- The glued bundled class function is integral because all of its elementary restrictions are.
      apply
        Representation.classFunction_mem_characterRing_of_restrict_mem_on_elementarySubgroups
          X hXelem φ
      intro H
      rw [hφ H]
      exact (ψ H).property
    refine ⟨⟨(φ : G → ℂ), hφ_mem⟩, ?_⟩
    ext H x
    -- The reconstructed global character restricts back to the original family coordinatewise.
    simpa [f, Representation.characterRingRestriction_apply] using congrFun (hφ H) x

/-- Helper for Remark 11-11.1-3: once a left inverse for the integral restriction-family map is
chosen, the complementary projector on local families factors through the coherence-defect map.
-/
theorem characterRingRestriction_residual_factors_through_coherence_defect
    (X : Finset (Subgroup G))
    (hXelem : ∀ H : Subgroup G, H ∈ X ↔ IsElementary H)
    (s : ((H : X) → R(H.1)) →ₗ[ℤ] R(G))
    (hs : Function.LeftInverse s (Representation.characterRingRestriction X).toLinearMap) :
    ∃ q : LinearMap.range (elementary_coherence_defect X hXelem) →ₗ[ℤ] ((H : X) → R(H.1)),
      q.comp (elementary_coherence_defect X hXelem).rangeRestrict =
        (LinearMap.id : ((H : X) → R(H.1)) →ₗ[ℤ] ((H : X) → R(H.1))) -
          (Representation.characterRingRestriction X).toLinearMap.comp s := by
  let f : R(G) →ₗ[ℤ] ((H : X) → R(H.1)) := (Representation.characterRingRestriction X).toLinearMap
  let d : ((H : X) → R(H.1)) →ₗ[ℤ] elementary_coherence_target X hXelem :=
    elementary_coherence_defect X hXelem
  let r : ((H : X) → R(H.1)) →ₗ[ℤ] ((H : X) → R(H.1)) := LinearMap.id - f.comp s
  have hr_ker : LinearMap.ker d ≤ LinearMap.ker r := by
    intro y hy
    rw [LinearMap.mem_ker] at hy ⊢
    rcases (characterRingRestriction_exact_elementary_coherence_defect X hXelem y).1 hy with
      ⟨x, rfl⟩
    -- The residual projector vanishes on the image of the restriction-family map because `s`
    -- is a left inverse there.
    change f x - f (s (f x)) = 0
    rw [hs x]
    simp
  let qbar : (((H : X) → R(H.1)) ⧸ LinearMap.ker d) →ₗ[ℤ] ((H : X) → R(H.1)) :=
    (LinearMap.ker d).liftQ r hr_ker
  let q : LinearMap.range d →ₗ[ℤ] ((H : X) → R(H.1)) :=
    qbar.comp d.quotKerEquivRange.symm.toLinearMap
  refine ⟨q, LinearMap.ext fun y ↦ ?_⟩
  -- Quotient by `ker d` and then identify the quotient with `range d`.
  change qbar (d.quotKerEquivRange.symm (d.rangeRestrict y)) = r y
  have hyq : d.quotKerEquivRange.symm (d.rangeRestrict y) = (LinearMap.ker d).mkQ y := by
    exact LinearMap.quotKerEquivRange_symm_apply_image (f := d) y ⟨y, rfl⟩
  rw [hyq]
  rfl

/-- Helper for Remark 11-11.1-3: the tensor coherence target records the restriction and
conjugation defects of a family `φ_H ∈ A ⊗ R(H)`. -/
abbrev tensorElementaryCoherenceTarget
    (X : Finset (Subgroup G))
    (_hXelem : ∀ H : Subgroup G, H ∈ X ↔ IsElementary H) :=
  (∀ p : elementary_restriction_relation X, A ⊗R(p.1.2.1)) ×
    (∀ q : elementary_conjugation_relation X, A ⊗R(q.2 •ᶜ q.1.1))

/-- Helper for Remark 11-11.1-3: the tensor defect map vanishes exactly on coherent local tensor
families. -/
def tensorElementaryCoherenceDefect
    (X : Finset (Subgroup G))
    (hXelem : ∀ H : Subgroup G, H ∈ X ↔ IsElementary H) :
    ((H : X) → (A ⊗R(H.1))) →ₗ[A]
      ((∀ p : elementary_restriction_relation X, A ⊗R(p.1.2.1)) ×
        (∀ q : elementary_conjugation_relation X, A ⊗R(q.2 •ᶜ q.1.1))) :=
  let restrictionDefect :
      ((H : X) → (A ⊗R(H.1))) →ₗ[A] ∀ p : elementary_restriction_relation X, A ⊗R(p.1.2.1) :=
    LinearMap.pi fun p =>
      let projH : ((H : X) → (A ⊗R(H.1))) →ₗ[A] A ⊗R(p.1.1.1) :=
        LinearMap.proj (R := A) (φ := fun H : X ↦ A ⊗R(H.1)) p.1.1
      let projH' : ((H : X) → (A ⊗R(H.1))) →ₗ[A] A ⊗R(p.1.2.1) :=
        LinearMap.proj (R := A) (φ := fun H : X ↦ A ⊗R(H.1)) p.1.2
      (Subgroup.tensorCharacterRingRestrictionOfLe (A := A) p.2).comp projH - projH'
  let conjugationDefect :
      ((H : X) → (A ⊗R(H.1))) →ₗ[A] ∀ q : elementary_conjugation_relation X, A ⊗R(q.2 •ᶜ q.1.1) :=
    LinearMap.pi fun q =>
      let qH : X := ⟨q.2 •ᶜ q.1.1, elementary_mem_of_conj X hXelem q.1.2 q.2⟩
      let projH : ((H : X) → (A ⊗R(H.1))) →ₗ[A] A ⊗R(q.1.1) :=
        LinearMap.proj (R := A) (φ := fun H : X ↦ A ⊗R(H.1)) q.1
      (Subgroup.conjugateTensorCharacterRingTransport (A := A) q.1.1 q.2).comp projH -
        LinearMap.proj (R := A) (φ := fun H : X ↦ A ⊗R(H.1)) qH
  LinearMap.prod restrictionDefect conjugationDefect

/-- Helper for Remark 11-11.1-3: the hypotheses `hres` and `hconj` say exactly that the tensor
coherence defect vanishes. -/
theorem tensorElementaryCoherenceDefect_eq_zero_of_coherent_family
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
    tensorElementaryCoherenceDefect (A := A) X hXelem φX =
      ((fun _ => 0), fun _ => 0) := by
  apply Prod.ext
  · funext p
    -- The first defect block is exactly the restriction-compatibility equation.
    simpa [tensorElementaryCoherenceDefect] using sub_eq_zero.mpr (hres p.2)
  · funext q
    -- The second defect block is exactly the conjugation-compatibility equation.
    simpa [tensorElementaryCoherenceDefect] using
      sub_eq_zero.mpr (hconj q.1 q.2 (elementary_mem_of_conj X hXelem q.1.2 q.2))

/-- Helper for Remark 11-11.1-3: coherence already kills the range-restricted tensor defect. -/
theorem tensor_coherence_defect_rangeRestrict_eq_zero_of_coherent_family
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
    (tensorElementaryCoherenceDefect (A := A) X hXelem).rangeRestrict φX = 0 := by
  -- Passing to the actual range does not change the underlying vanishing statement.
  apply Subtype.ext
  -- Rewrite the target zero explicitly to avoid typeclass search on the large product type.
  change tensorElementaryCoherenceDefect (A := A) X hXelem φX = ((fun _ => 0), fun _ => 0)
  exact
    tensorElementaryCoherenceDefect_eq_zero_of_coherent_family
      (A := A) X hXelem φX hres hconj

/-- Helper for Remark 11-11.1-3: after commuting tensor product with the finite restriction-family
product, the tensor restriction-family map is exactly the base change of the integral
restriction-family map. -/
noncomputable abbrev tensorCharacterRingRestrictionFamilyEquiv
    (X : Finset (Subgroup G)) :
    TensorProduct ℤ A ((H : X) → R(H.1)) ≃ₗ[A] ((H : X) → (A ⊗R(H.1))) := by
  classical
  exact TensorProduct.piRight ℤ A A (fun H : X ↦ R(H.1))

/-- Helper for Remark 11-11.1-3: tensor product commutes with the finite family of restriction
coordinates indexed by subgroup inclusions. -/
noncomputable abbrev tensorElementaryRestrictionEquiv
    (X : Finset (Subgroup G)) :
    TensorProduct ℤ A (∀ p : elementary_restriction_relation X, R(p.1.2.1)) ≃ₗ[A]
      (∀ p : elementary_restriction_relation X, A ⊗R(p.1.2.1)) := by
  classical
  exact TensorProduct.piRight ℤ A A (fun p : elementary_restriction_relation X ↦ R(p.1.2.1))

/-- Helper for Remark 11-11.1-3: tensor product commutes with the finite family of conjugation
coordinates indexed by elementary subgroups. -/
noncomputable abbrev tensorElementaryConjugationEquiv
    (X : Finset (Subgroup G)) :
    TensorProduct ℤ A (∀ q : elementary_conjugation_relation X, R(q.2 •ᶜ q.1.1)) ≃ₗ[A]
      (∀ q : elementary_conjugation_relation X, A ⊗R(q.2 •ᶜ q.1.1)) := by
  classical
  letI : Fintype G := Fintype.ofFinite G
  exact TensorProduct.piRight ℤ A A (fun q : elementary_conjugation_relation X ↦ R(q.2 •ᶜ q.1.1))

/-- Helper for Remark 11-11.1-3: tensor product commutes with the full elementary coherence
target. -/
noncomputable abbrev tensorElementaryCoherenceEquiv
    (X : Finset (Subgroup G))
    (hXelem : ∀ H : Subgroup G, H ∈ X ↔ IsElementary H) :
    TensorProduct ℤ A (elementary_coherence_target X hXelem) ≃ₗ[A]
      ((∀ p : elementary_restriction_relation X, A ⊗R(p.1.2.1)) ×
        (∀ q : elementary_conjugation_relation X, A ⊗R(q.2 •ᶜ q.1.1))) := by
  classical
  letI : Fintype G := Fintype.ofFinite G
  exact
    (TensorProduct.prodRight ℤ A A
      (∀ p : elementary_restriction_relation X, R(p.1.2.1))
      (∀ q : elementary_conjugation_relation X, R(q.2 •ᶜ q.1.1))).trans
      (LinearEquiv.prodCongr
        (tensorElementaryRestrictionEquiv (A := A) X)
        (tensorElementaryConjugationEquiv (A := A) X))

/-- Helper for Remark 11-11.1-3: after commuting tensor product with the finite restriction-family
product, the tensor restriction-family map is exactly the base change of the integral
restriction-family map. -/
theorem tensor_characterRingRestriction_family_eq_baseChange
    (X : Finset (Subgroup G)) :
    LinearMap.pi (fun H : X ↦ Subgroup.tensorCharacterRingRestriction (A := A) H.1) =
      (tensorCharacterRingRestrictionFamilyEquiv (A := A) X).toLinearMap.comp
        ((Representation.characterRingRestriction X).toLinearMap.baseChange A) := by
  classical
  apply TensorProduct.AlgebraTensorModule.ext
  intro a χ
  ext H
  -- On pure tensors, both maps restrict `χ` to `H` and keep the scalar `a` unchanged.
  simp [Representation.characterRingRestriction, Subgroup.tensorCharacterRingRestriction,
    tensorCharacterRingRestrictionFamilyEquiv, LinearMap.baseChange_tmul, TensorProduct.piRightHom_tmul]

-- The tensor-product comparison proof expands several `TensorProduct.induction_on` branches;
-- each branch lives in its own private lemma so that every declaration stays within the
-- default elaboration budget.
/-- Branch helper (zero case) for `tensorElementaryCoherenceDefect_eq_baseChange`. -/
private theorem tensorElementaryCoherenceDefect_baseChange_zero_local
    (X : Finset (Subgroup G))
    (hXelem : ∀ H : Subgroup G, H ∈ X ↔ IsElementary H) :
    tensorElementaryCoherenceDefect (A := A) X hXelem
        (tensorCharacterRingRestrictionFamilyEquiv (A := A) X 0) =
      (((tensorElementaryCoherenceEquiv (A := A) X hXelem).toLinearMap.comp
            ((elementary_coherence_defect X hXelem).baseChange A)).comp
          (tensorCharacterRingRestrictionFamilyEquiv (A := A) X).symm.toLinearMap)
        (tensorCharacterRingRestrictionFamilyEquiv (A := A) X 0) := by
  classical
  simp only [LinearEquiv.map_zero, LinearMap.map_zero]

/-- Branch helper (pure-tensor case, restriction coordinates) for
`tensorElementaryCoherenceDefect_eq_baseChange`. -/
private theorem tensorElementaryCoherenceDefect_baseChange_tmul_fst_local
    (X : Finset (Subgroup G))
    (hXelem : ∀ H : Subgroup G, H ∈ X ↔ IsElementary H)
    (a : A) (χ : (H : X) → R(H.1)) :
    (tensorElementaryCoherenceDefect (A := A) X hXelem
        (tensorCharacterRingRestrictionFamilyEquiv (A := A) X (a ⊗ₜ[ℤ] χ))).1 =
      ((((tensorElementaryCoherenceEquiv (A := A) X hXelem).toLinearMap.comp
            ((elementary_coherence_defect X hXelem).baseChange A)).comp
          (tensorCharacterRingRestrictionFamilyEquiv (A := A) X).symm.toLinearMap)
        (tensorCharacterRingRestrictionFamilyEquiv (A := A) X (a ⊗ₜ[ℤ] χ))).1 := by
  classical
  funext p
  -- On pure tensors, both sides record the same restriction defect in the `p`-coordinate.
  simpa [tensorElementaryCoherenceDefect, elementary_coherence_defect,
    tensorElementaryCoherenceEquiv, tensorElementaryRestrictionEquiv,
    tensorElementaryConjugationEquiv, tensorCharacterRingRestrictionFamilyEquiv,
    TensorProduct.prodRight_tmul] using
    (TensorProduct.tmul_sub a
      ((Subgroup.characterRingRestrictionOfLe p.2) (χ p.1.1))
      (χ p.1.2)).symm

/-- Branch helper (pure-tensor case, conjugation coordinates) for
`tensorElementaryCoherenceDefect_eq_baseChange`. -/
private theorem tensorElementaryCoherenceDefect_baseChange_tmul_snd_local
    (X : Finset (Subgroup G))
    (hXelem : ∀ H : Subgroup G, H ∈ X ↔ IsElementary H)
    (a : A) (χ : (H : X) → R(H.1)) :
    (tensorElementaryCoherenceDefect (A := A) X hXelem
        (tensorCharacterRingRestrictionFamilyEquiv (A := A) X (a ⊗ₜ[ℤ] χ))).2 =
      ((((tensorElementaryCoherenceEquiv (A := A) X hXelem).toLinearMap.comp
            ((elementary_coherence_defect X hXelem).baseChange A)).comp
          (tensorCharacterRingRestrictionFamilyEquiv (A := A) X).symm.toLinearMap)
        (tensorCharacterRingRestrictionFamilyEquiv (A := A) X (a ⊗ₜ[ℤ] χ))).2 := by
  classical
  funext q
  -- On pure tensors, both sides record the same conjugation defect in the `q`-coordinate.
  simpa [tensorElementaryCoherenceDefect, elementary_coherence_defect,
    tensorElementaryCoherenceEquiv, tensorElementaryConjugationEquiv,
    tensorCharacterRingRestrictionFamilyEquiv, TensorProduct.prodRight_tmul] using
    (TensorProduct.tmul_sub a
      ((Subgroup.characterRingTransport ((MulAut.conj q.2).subgroupMap q.1.1).symm)
        (χ q.1))
      (χ ⟨q.2 •ᶜ q.1.1, elementary_mem_of_conj X hXelem q.1.2 q.2⟩)).symm

/-- Branch helper (additive case) for `tensorElementaryCoherenceDefect_eq_baseChange`. -/
private theorem tensorElementaryCoherenceDefect_baseChange_add_local
    (X : Finset (Subgroup G))
    (hXelem : ∀ H : Subgroup G, H ∈ X ↔ IsElementary H)
    (w w' : TensorProduct ℤ A ((H : X) → R(H.1)))
    (hw : tensorElementaryCoherenceDefect (A := A) X hXelem
        (tensorCharacterRingRestrictionFamilyEquiv (A := A) X w) =
      (((tensorElementaryCoherenceEquiv (A := A) X hXelem).toLinearMap.comp
            ((elementary_coherence_defect X hXelem).baseChange A)).comp
          (tensorCharacterRingRestrictionFamilyEquiv (A := A) X).symm.toLinearMap)
        (tensorCharacterRingRestrictionFamilyEquiv (A := A) X w))
    (hw' : tensorElementaryCoherenceDefect (A := A) X hXelem
        (tensorCharacterRingRestrictionFamilyEquiv (A := A) X w') =
      (((tensorElementaryCoherenceEquiv (A := A) X hXelem).toLinearMap.comp
            ((elementary_coherence_defect X hXelem).baseChange A)).comp
          (tensorCharacterRingRestrictionFamilyEquiv (A := A) X).symm.toLinearMap)
        (tensorCharacterRingRestrictionFamilyEquiv (A := A) X w')) :
    tensorElementaryCoherenceDefect (A := A) X hXelem
        (tensorCharacterRingRestrictionFamilyEquiv (A := A) X (w + w')) =
      (((tensorElementaryCoherenceEquiv (A := A) X hXelem).toLinearMap.comp
            ((elementary_coherence_defect X hXelem).baseChange A)).comp
          (tensorCharacterRingRestrictionFamilyEquiv (A := A) X).symm.toLinearMap)
        (tensorCharacterRingRestrictionFamilyEquiv (A := A) X (w + w')) := by
  classical
  simp only [LinearEquiv.map_add, LinearMap.map_add]
  congr 1

/-- Helper for Remark 11-11.1-3: after commuting tensor product with the finite source and target
products, the tensor coherence defect is exactly the base change of the integral coherence defect.
-/
theorem tensorElementaryCoherenceDefect_eq_baseChange
    (X : Finset (Subgroup G))
    (hXelem : ∀ H : Subgroup G, H ∈ X ↔ IsElementary H) :
    tensorElementaryCoherenceDefect (A := A) X hXelem =
      ((tensorElementaryCoherenceEquiv (A := A) X hXelem).toLinearMap.comp
        ((elementary_coherence_defect X hXelem).baseChange A)).comp
        (tensorCharacterRingRestrictionFamilyEquiv (A := A) X).symm.toLinearMap := by
  classical
  have hmain :
      ∀ w : TensorProduct ℤ A ((H : X) → R(H.1)),
        tensorElementaryCoherenceDefect (A := A) X hXelem
            (tensorCharacterRingRestrictionFamilyEquiv (A := A) X w) =
          (((tensorElementaryCoherenceEquiv (A := A) X hXelem).toLinearMap.comp
                ((elementary_coherence_defect X hXelem).baseChange A)).comp
              (tensorCharacterRingRestrictionFamilyEquiv (A := A) X).symm.toLinearMap)
            (tensorCharacterRingRestrictionFamilyEquiv (A := A) X w) := by
    intro w
    induction w using TensorProduct.induction_on with
    | zero => exact tensorElementaryCoherenceDefect_baseChange_zero_local X hXelem
    | tmul a χ =>
        exact Prod.ext
          (tensorElementaryCoherenceDefect_baseChange_tmul_fst_local X hXelem a χ)
          (tensorElementaryCoherenceDefect_baseChange_tmul_snd_local X hXelem a χ)
    | add w w' hw hw' =>
        exact tensorElementaryCoherenceDefect_baseChange_add_local X hXelem w w' hw hw'
  exact
    LinearMap.ext fun φ ↦ by
      simpa using hmain ((tensorCharacterRingRestrictionFamilyEquiv (A := A) X).symm φ)

/-- Helper for Remark 11-11.1-3: the elementary coherence-defect target is a finite product of
finitely generated character rings.
-/
theorem elementary_coherence_target_moduleFinite
    (X : Finset (Subgroup G))
    (hXelem : ∀ H : Subgroup G, H ∈ X ↔ IsElementary H) :
    Module.Finite ℤ (elementary_coherence_target X hXelem) := by
  classical
  letI : Fintype G := Fintype.ofFinite G
  letI : ∀ p : elementary_restriction_relation X, Module.Finite ℤ (R(p.1.2.1)) :=
    fun p ↦ show Module.Finite ℤ (R(p.1.2.1)) from characterRing_moduleFinite
  letI : ∀ q : elementary_conjugation_relation X, Module.Finite ℤ (R(q.2 •ᶜ q.1.1)) :=
    fun q ↦ show Module.Finite ℤ (R(q.2 •ᶜ q.1.1)) from characterRing_moduleFinite
  letI : Module.Finite ℤ (∀ p : elementary_restriction_relation X, R(p.1.2.1)) :=
    Module.Finite.pi
  letI : Module.Finite ℤ (∀ q : elementary_conjugation_relation X, R(q.2 •ᶜ q.1.1)) :=
    Module.Finite.pi
  -- The coherence target is a finite product of finitely generated character rings.
  exact Module.Finite.prod

/-- Helper for Remark 11-11.1-3: nonzero integer multiplication is injective on each local
character ring. -/
theorem characterRing_zsmul_left_cancel
    (H : Subgroup G) {ξ η : R(H)} {n : ℤ} (hn : n ≠ 0)
    (h : n • ξ = n • η) :
    ξ = η := by
  apply Subtype.ext
  ext x
  have hvalue := congrArg (fun z : R(H) ↦ ((z : H → ℂ) x)) h
  have hnC : (n : ℂ) ≠ 0 := by
    exact_mod_cast hn
  -- Evaluate in `ℂ`, where multiplication by a nonzero integer is cancellable.
  exact mul_left_cancel₀ hnC <| by
    simpa [zsmul_eq_mul] using hvalue

/-- Helper for Remark 11-11.1-3: a preimage of `n • t` can be normalized so that the chosen
restriction splitting removes its global component without changing its coherence defect. -/
theorem residual_family_of_multiple_coherence_defect
    (X : Finset (Subgroup G))
    (hXelem : ∀ H : Subgroup G, H ∈ X ↔ IsElementary H)
    (s : ((H : X) → R(H.1)) →ₗ[ℤ] R(G))
    (hs : Function.LeftInverse s (Representation.characterRingRestriction X).toLinearMap)
    {t : elementary_coherence_target X hXelem} {n : ℤ}
    (ht : n • t ∈ LinearMap.range (elementary_coherence_defect X hXelem)) :
    ∃ x : (H : X) → R(H.1),
      s x = 0 ∧ elementary_coherence_defect X hXelem x = n • t := by
  let f : R(G) →ₗ[ℤ] ((H : X) → R(H.1)) := (Representation.characterRingRestriction X).toLinearMap
  let d : ((H : X) → R(H.1)) →ₗ[ℤ] elementary_coherence_target X hXelem :=
    elementary_coherence_defect X hXelem
  have hExact : Function.Exact f d :=
    characterRingRestriction_exact_elementary_coherence_defect X hXelem
  have hcomp : d.comp f = 0 := hExact.linearMap_comp_eq_zero
  rcases ht with ⟨ψ, hψ⟩
  refine ⟨ψ - f (s ψ), ?_, ?_⟩
  · -- Subtracting the lifted global part leaves a purely residual family.
    rw [map_sub, hs]
    simp
  · -- Exactness kills the removed global term, so the defect remains `n • t`.
    have hfzero : d (f (s ψ)) = 0 := by
      have hcomp_apply := congrArg
        (fun m : R(G) →ₗ[ℤ] elementary_coherence_target X hXelem ↦ m (s ψ)) hcomp
      change d (f (s ψ)) = (0 : elementary_coherence_target X hXelem) at hcomp_apply
      exact hcomp_apply
    calc
      d (ψ - f (s ψ)) = d ψ - d (f (s ψ)) := by simp
      _ = n • t - 0 := by rw [hψ, hfzero]
      _ = n • t := by simp


end CharacterizationOfCharacters

end Representation
