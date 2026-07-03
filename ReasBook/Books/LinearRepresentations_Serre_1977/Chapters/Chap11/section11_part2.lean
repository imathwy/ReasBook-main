import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Remark_11_11_1_3 (from Chap11) -/
noncomputable section

universe v

namespace Representation

section CharacterizationOfCharacters

open scoped Pointwise Representation SubgroupInduction TensorProduct

variable {G : Type} [Group G] [Finite G]
variable {A : Type v} [CommRing A]

local notation:max s " •ᶜ " H => (MulAut.conj s • H : Subgroup G)

/-- Helper for Remark 11-11.1-3: every subgroup of a finite group is finite. -/
local instance (H : Subgroup G) : Fintype H := Fintype.ofFinite H

/-- Helper for Remark 11-11.1-3: inclusion relations among the elementary-indexed local
character-ring coordinates. -/
private abbrev elementary_restriction_relation (X : Finset (Subgroup G)) :=
  { p : X × X // p.2.1 ≤ p.1.1 }

/-- Helper for Remark 11-11.1-3: conjugation relations among the elementary-indexed local
character-ring coordinates. -/
private abbrev elementary_conjugation_relation (X : Finset (Subgroup G)) :=
  X × G

/-- Helper for Remark 11-11.1-3: the codomain collecting all restriction and conjugation defects
for an integral family on the elementary subgroups. -/
private abbrev elementary_coherence_target
    (X : Finset (Subgroup G))
    (_hXelem : ∀ H : Subgroup G, H ∈ X ↔ IsElementary H) :=
  (∀ p : elementary_restriction_relation X, R(p.1.2.1)) ×
    (∀ q : elementary_conjugation_relation X, R(q.2 •ᶜ q.1.1))

/-- Helper for Remark 11-11.1-3: transporting the global restriction of a character along
conjugation agrees with restricting the same global character to the conjugate subgroup. -/
private theorem characterRingTransport_global_restriction_eq_conjugate
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
private def elementary_coherence_defect
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
private theorem characterRingRestriction_exact_elementary_coherence_defect
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
        Subgroup.characterRingOverFieldRestrictionOfLe_apply]
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
private theorem characterRingRestriction_residual_factors_through_coherence_defect
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
private abbrev tensorElementaryCoherenceTarget
    (X : Finset (Subgroup G))
    (_hXelem : ∀ H : Subgroup G, H ∈ X ↔ IsElementary H) :=
  (∀ p : elementary_restriction_relation X, A ⊗R(p.1.2.1)) ×
    (∀ q : elementary_conjugation_relation X, A ⊗R(q.2 •ᶜ q.1.1))

/-- Helper for Remark 11-11.1-3: the tensor defect map vanishes exactly on coherent local tensor
families. -/
private def tensorElementaryCoherenceDefect
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
private theorem tensorElementaryCoherenceDefect_eq_zero_of_coherent_family
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
private theorem tensor_coherence_defect_rangeRestrict_eq_zero_of_coherent_family
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
private noncomputable abbrev tensorCharacterRingRestrictionFamilyEquiv
    (X : Finset (Subgroup G)) :
    TensorProduct ℤ A ((H : X) → R(H.1)) ≃ₗ[A] ((H : X) → (A ⊗R(H.1))) := by
  classical
  exact TensorProduct.piRight ℤ A A (fun H : X ↦ R(H.1))

/-- Helper for Remark 11-11.1-3: tensor product commutes with the finite family of restriction
coordinates indexed by subgroup inclusions. -/
private noncomputable abbrev tensorElementaryRestrictionEquiv
    (X : Finset (Subgroup G)) :
    TensorProduct ℤ A (∀ p : elementary_restriction_relation X, R(p.1.2.1)) ≃ₗ[A]
      (∀ p : elementary_restriction_relation X, A ⊗R(p.1.2.1)) := by
  classical
  exact TensorProduct.piRight ℤ A A (fun p : elementary_restriction_relation X ↦ R(p.1.2.1))

/-- Helper for Remark 11-11.1-3: tensor product commutes with the finite family of conjugation
coordinates indexed by elementary subgroups. -/
private noncomputable abbrev tensorElementaryConjugationEquiv
    (X : Finset (Subgroup G)) :
    TensorProduct ℤ A (∀ q : elementary_conjugation_relation X, R(q.2 •ᶜ q.1.1)) ≃ₗ[A]
      (∀ q : elementary_conjugation_relation X, A ⊗R(q.2 •ᶜ q.1.1)) := by
  classical
  letI : Fintype G := Fintype.ofFinite G
  exact TensorProduct.piRight ℤ A A (fun q : elementary_conjugation_relation X ↦ R(q.2 •ᶜ q.1.1))

/-- Helper for Remark 11-11.1-3: tensor product commutes with the full elementary coherence
target. -/
private noncomputable abbrev tensorElementaryCoherenceEquiv
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
private theorem tensor_characterRingRestriction_family_eq_baseChange
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

-- The tensor-product comparison proof expands several `TensorProduct.induction_on` branches.
set_option maxHeartbeats 5000000 in
set_option synthInstance.maxHeartbeats 2000000 in
/-- Helper for Remark 11-11.1-3: after commuting tensor product with the finite source and target
products, the tensor coherence defect is exactly the base change of the integral coherence defect.
-/
private theorem tensorElementaryCoherenceDefect_eq_baseChange
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
    | zero =>
        rw [show tensorCharacterRingRestrictionFamilyEquiv (A := A) X 0 = 0 by
          exact (tensorCharacterRingRestrictionFamilyEquiv (A := A) X).toLinearMap.map_zero]
        rw [LinearMap.map_zero, LinearMap.comp_apply]
        rw [show (tensorCharacterRingRestrictionFamilyEquiv (A := A) X).symm.toLinearMap 0 = 0 by
          exact (tensorCharacterRingRestrictionFamilyEquiv (A := A) X).symm.toLinearMap.map_zero]
        rw [LinearMap.comp_apply, LinearMap.map_zero]
        exact (tensorElementaryCoherenceEquiv (A := A) X hXelem).toLinearMap.map_zero
    | tmul a χ =>
        apply Prod.ext
        · funext p
          -- On pure tensors, both sides record the same restriction defect in the `p`-coordinate.
          simpa [tensorElementaryCoherenceDefect, elementary_coherence_defect,
            tensorElementaryCoherenceEquiv, tensorElementaryRestrictionEquiv,
            tensorElementaryConjugationEquiv, tensorCharacterRingRestrictionFamilyEquiv,
            TensorProduct.prodRight_tmul] using
            (TensorProduct.tmul_sub a
              ((Subgroup.characterRingRestrictionOfLe p.2) (χ p.1.1))
              (χ p.1.2)).symm
        · funext q
          -- On pure tensors, both sides record the same conjugation defect in the `q`-coordinate.
          simpa [tensorElementaryCoherenceDefect, elementary_coherence_defect,
            tensorElementaryCoherenceEquiv, tensorElementaryConjugationEquiv,
            tensorCharacterRingRestrictionFamilyEquiv, TensorProduct.prodRight_tmul] using
            (TensorProduct.tmul_sub a
              ((Subgroup.characterRingTransport ((MulAut.conj q.2).subgroupMap q.1.1).symm)
                (χ q.1))
              (χ ⟨q.2 •ᶜ q.1.1, elementary_mem_of_conj X hXelem q.1.2 q.2⟩)).symm
    | add w w' hw hw' =>
        rw [show
          tensorCharacterRingRestrictionFamilyEquiv (A := A) X (w + w') =
            tensorCharacterRingRestrictionFamilyEquiv (A := A) X w +
              tensorCharacterRingRestrictionFamilyEquiv (A := A) X w' by
          simpa using
            (tensorCharacterRingRestrictionFamilyEquiv (A := A) X).toLinearMap.map_add w w']
        rw [LinearMap.map_add, LinearMap.comp_apply, LinearMap.map_add,
          LinearMap.comp_apply, LinearMap.map_add]
        rw [hw, hw']
        simpa [LinearMap.comp_apply, LinearEquiv.apply_symm_apply] using
          ((tensorElementaryCoherenceEquiv (A := A) X hXelem).toLinearMap.map_add
            (((elementary_coherence_defect X hXelem).baseChange A) w)
            (((elementary_coherence_defect X hXelem).baseChange A) w')).symm
  exact
    LinearMap.ext fun φ ↦ by
      simpa using hmain ((tensorCharacterRingRestrictionFamilyEquiv (A := A) X).symm φ)

/-- Helper for Remark 11-11.1-3: the elementary coherence-defect target is a finite product of
finitely generated character rings.
-/
private theorem elementary_coherence_target_moduleFinite
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
private theorem characterRing_zsmul_left_cancel
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
private theorem residual_family_of_multiple_coherence_defect
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
    simp [f, hs]
  · -- Exactness kills the removed global term, so the defect remains `n • t`.
    have hfzero : d (f (s ψ)) = 0 := by
      simpa using LinearMap.congr_fun hcomp (s ψ)
    calc
      d (ψ - f (s ψ)) = d ψ - d (f (s ψ)) := by simp
      _ = n • t - 0 := by rw [hψ, hfzero]
      _ = n • t := by simp

/-- Helper for Remark 11-11.1-3: subgroups of elementary groups are elementary. -/
private theorem subgroup_isElementary_of_isElementary_local
    {H : Type*} [Group H] (K : Subgroup H) (hH : IsElementary H) :
    IsElementary K := by
  rcases hH with ⟨p, hpH⟩
  rcases hpH with ⟨C, P, hCP⟩
  letI : Fact (Nat.Prime p) := ⟨hCP.prime⟩
  letI : Finite H := (show IsPElementary p H from ⟨C, P, hCP⟩).finite
  letI : Finite K := Finite.of_injective ((↑) : K → H) Subtype.val_injective
  let C' : Subgroup K := (K ⊓ C).subgroupOf K
  let P' : Subgroup K := (K ⊓ P).subgroupOf K
  letI : Finite ↥C' := Finite.of_injective ((↑) : C' → K) Subtype.val_injective
  letI : Finite ↥P' := Finite.of_injective ((↑) : P' → K) Subtype.val_injective
  have hC'card : Nat.card ↥C' = Nat.card ↥(K ⊓ C) := by
    exact Nat.card_congr
      (Subgroup.subgroupOfEquivOfLe (show K ⊓ C ≤ K from inf_le_left)).toEquiv
  -- Restrict the elementary decomposition of `H` to the chosen subgroup `K`.
  refine ⟨p, C', P', ?_⟩
  refine ⟨hCP.prime, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · infer_instance
  · letI : IsCyclic ↥C := hCP.cyclic
    letI : IsCyclic ↥(K ⊓ C) :=
      Subgroup.isCyclic_of_le (show K ⊓ C ≤ C from inf_le_right)
    exact
      isCyclic_of_surjective
        (Subgroup.subgroupOfEquivOfLe (show K ⊓ C ≤ K from inf_le_left)).symm.toMonoidHom
        (Subgroup.subgroupOfEquivOfLe (show K ⊓ C ≤ K from inf_le_left)).symm.surjective
  · have hdiv : Nat.card ↥(K ⊓ C) ∣ Nat.card ↥C := by
      exact Subgroup.card_dvd_of_le (show K ⊓ C ≤ C from inf_le_right)
    rw [hC'card]
    exact hCP.coprime_card.of_dvd_right hdiv
  · have hPsub : IsPGroup p ↥((K ⊓ P).subgroupOf P) := by
      exact hCP.isPGroup.to_subgroup ((K ⊓ P).subgroupOf P)
    have hPinf_right : IsPGroup p ↥(K ⊓ P) := by
      exact hPsub.of_equiv
        (Subgroup.subgroupOfEquivOfLe (show K ⊓ P ≤ P from inf_le_right))
    exact hPinf_right.of_equiv
      (Subgroup.subgroupOfEquivOfLe (show K ⊓ P ≤ K from inf_le_left)).symm
  · intro c hc u hu
    have hcC : ((c : K) : H) ∈ C := by
      exact (show ((c : K) : H) ∈ K ⊓ C from hc).2
    have huP : ((u : K) : H) ∈ P := by
      exact (show ((u : K) : H) ∈ K ⊓ P from hu).2
    apply Subtype.ext
    simpa using hCP.centralizes hcC ((u : K) : H) huP
  · refine Subgroup.isComplement'_of_disjoint_and_mul_eq_univ ?_ ?_
    · rw [Subgroup.disjoint_def]
      intro x hxC hxP
      have hxCG : ((x : K) : H) ∈ C := by
        exact (show ((x : K) : H) ∈ K ⊓ C from hxC).2
      have hxPG : ((x : K) : H) ∈ P := by
        exact (show ((x : K) : H) ∈ K ⊓ P from hxP).2
      have hxbot : ((x : K) : H) ∈ (⊥ : Subgroup H) := by
        have hbot : C ⊓ P = (⊥ : Subgroup H) := disjoint_iff.mp hCP.isComplement.disjoint
        exact hbot ▸ ⟨hxCG, hxPG⟩
      apply Subtype.ext
      simpa using hxbot
    · apply Set.eq_univ_iff_forall.2
      intro x
      let xr : K := pRegularComponent p x
      let xu : K := pUnipotentComponent p x
      have hdecomp : IsPComponentDecomposition p x xu xr := by
        simpa [xu, xr] using
          p_component_decomposition_exists (p := p) x (isOfFinOrder_of_finite x)
      have hxrC : (xr : H) ∈ C := by
        have hxrReg : IsPRegular p (xr : H) := by
          simpa [IsPRegular, Subgroup.orderOf_mk, xr] using hdecomp.isPRegular
        change (xr : H) ∈ (C : Set H)
        rw [hCP.cyclic_factor_eq_setOf_isPRegular]
        exact hxrReg
      have hxuP : (xu : H) ∈ P := by
        have hxuElt : IsPElement p (xu : H) := by
          simpa [IsPElement, Subgroup.orderOf_mk, xu] using hdecomp.isPElement
        change (xu : H) ∈ (P : Set H)
        rw [hCP.p_group_factor_eq_setOf_isPElement]
        exact hxuElt
      have hxr_mem : xr ∈ C' := by
        change (xr : H) ∈ K ⊓ C
        exact ⟨xr.2, hxrC⟩
      have hxu_mem : xu ∈ P' := by
        change (xu : H) ∈ K ⊓ P
        exact ⟨xu.2, hxuP⟩
      refine ⟨xr, hxr_mem, xu, hxu_mem, ?_⟩
      calc
        xr * xu = xu * xr := by
          simpa using hdecomp.commute.symm
        _ = x := hdecomp.mul_eq

/-- Helper for Remark 11-11.1-3: elementary groups stay elementary under group isomorphisms. -/
private theorem isElementary_of_mulEquiv_local
    {H : Type*} [Group H] {J : Type*} [Group J]
    (e : H ≃* J) (hH : IsElementary H) :
    IsElementary J := by
  rcases hH with ⟨p, C, P, hCP⟩
  letI : Finite H := (show IsPElementary p H from ⟨C, P, hCP⟩).finite
  letI : Finite P := hCP.finite_pGroup_factor
  letI : Finite J := Finite.of_equiv H e.toEquiv
  letI : IsCyclic C := hCP.cyclic
  refine ⟨p, C.map e.toMonoidHom, P.map e.toMonoidHom, ?_⟩
  refine ⟨hCP.prime, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact Finite.of_equiv P (Subgroup.equivMapOfInjective P e.toMonoidHom e.injective)
  · let eC : C ≃* C.map e.toMonoidHom := Subgroup.equivMapOfInjective C e.toMonoidHom e.injective
    exact isCyclic_of_surjective eC eC.surjective
  · have hcard : Nat.card (C.map e.toMonoidHom) = Nat.card C :=
      (Nat.card_congr (Subgroup.equivMapOfInjective C e.toMonoidHom e.injective).toEquiv).symm
    exact hcard ▸ hCP.coprime_card
  · exact hCP.isPGroup.of_equiv (Subgroup.equivMapOfInjective P e.toMonoidHom e.injective)
  · intro c hc y hy
    rcases hc with ⟨c0, hc0, rfl⟩
    rcases hy with ⟨y0, hy0, rfl⟩
    simpa using congrArg e (hCP.centralizes hc0 y0 hy0)
  · have hcardC : Nat.card (C.map e.toMonoidHom) = Nat.card C :=
      (Nat.card_congr (Subgroup.equivMapOfInjective C e.toMonoidHom e.injective).toEquiv).symm
    have hcardP : Nat.card (P.map e.toMonoidHom) = Nat.card P :=
      (Nat.card_congr (Subgroup.equivMapOfInjective P e.toMonoidHom e.injective).toEquiv).symm
    have hcardJ : Nat.card H = Nat.card J := Nat.card_congr e.toEquiv
    refine Subgroup.isComplement'_of_card_mul_and_disjoint ?_ ?_
    · calc
        Nat.card (C.map e.toMonoidHom) * Nat.card (P.map e.toMonoidHom)
            = Nat.card C * Nat.card P := by rw [hcardC, hcardP]
        _ = Nat.card H := hCP.isComplement.card_mul
        _ = Nat.card J := hcardJ
    · rw [disjoint_iff, ← Subgroup.map_inf C P e.toMonoidHom e.injective,
        disjoint_iff.mp hCP.isComplement.disjoint, Subgroup.map_bot]

/-- Helper for Remark 11-11.1-3: the mapped subgroup `K.map H.subtype` lies inside `H`. -/
private theorem subgroup_chain_map_le_local
    (H : Subgroup G) (K : Subgroup H) :
    K.map H.subtype ≤ H := by
  -- Every element of the mapped subgroup is literally the image of an element of `K ≤ H`.
  intro x hx
  rcases hx with ⟨y, -, rfl⟩
  exact y.property

/-- Helper for Remark 11-11.1-3: restricting a mapped subgroup back along the ambient inclusion
recovers the original subgroup. -/
private theorem subgroup_chain_inner_subgroup_eq_local
    (H : Subgroup G) (K : Subgroup H) :
    ((K.map H.subtype).subgroupOf H : Subgroup H) = K := by
  -- The image subgroup consists exactly of those elements of `H` coming from `K`.
  ext k
  change k.1 ∈ K.map H.subtype ↔ k ∈ K
  constructor
  · intro hk
    rcases hk with ⟨x, hx, hxk⟩
    have hxeq : x = k := by
      apply Subtype.ext
      simpa using hxk
    simpa [hxeq] using hx
  · intro hk
    exact ⟨k, hk, rfl⟩

/-- Helper for Remark 11-11.1-3: mapping a subgroup-of-subgroup back to the ambient group gives
the original subgroup. -/
private theorem subgroup_chain_map_subgroupOf_eq_local
    (H : Subgroup G) (L : Subgroup G) (hL : L ≤ H) :
    ((L.subgroupOf H).map H.subtype : Subgroup G) = L := by
  -- Passing to `subgroupOf H` only changes the ambient type; mapping back undoes that change.
  ext x
  constructor
  · intro hx
    rcases hx with ⟨y, hy, rfl⟩
    exact hy
  · intro hx
    exact ⟨⟨x, hL hx⟩, hx, rfl⟩

/-- Helper for Remark 11-11.1-3: if `J ≤ M` and the subgroup cut out by `J` inside `M` is all
of `M`, then `J` already equals `M`. -/
private theorem subgroup_eq_of_le_of_subgroupOf_eq_top_local
    {H0 : Type*} [Group H0]
    (M J : Subgroup H0) (hJM : J ≤ M) (hJtop : J.subgroupOf M = ⊤) :
    J = M := by
  have hmap :
      ((J.subgroupOf M).map M.subtype : Subgroup H0) = J :=
    subgroup_chain_map_subgroupOf_eq_local (G := H0) M J hJM
  have htop_subgroupOf : (M.subgroupOf M : Subgroup M) = ⊤ := by
    -- Inside `M`, the subgroup cut out by `M` itself is the top subgroup.
    ext x
    simp
  have htop_map : (((⊤ : Subgroup M).map M.subtype : Subgroup H0)) = M := by
    -- Map the tautological top subgroup of `M` back to the ambient group.
    rw [← htop_subgroupOf]
    simpa using (subgroup_chain_map_subgroupOf_eq_local (G := H0) M M le_rfl)
  -- Map the `subgroupOf` equality back to the ambient group, then identify the mapped top with
  -- `M`.
  calc
    J = ((J.subgroupOf M).map M.subtype : Subgroup H0) := hmap.symm
    _ = ((⊤ : Subgroup M).map M.subtype : Subgroup H0) := by rw [hJtop]
    _ = M := htop_map

/-- Helper for Remark 11-11.1-3: mapping a subgroup along an injective subgroup inclusion does not
change its cardinality. -/
private theorem subgroup_chain_map_card_eq_local
    (H : Subgroup G) (K : Subgroup H) :
    Nat.card (K.map H.subtype) = Nat.card K := by
  -- The mapped subgroup is canonically equivalent to the original subgroup through the injective
  -- ambient inclusion.
  exact Nat.card_congr (K.equivMapOfInjective H.subtype H.subtype_injective).toEquiv

/-- Helper for Remark 11-11.1-3: every proper subgroup of a finite ambient subgroup has strictly
smaller cardinality. -/
private theorem subgroup_card_lt_of_lt_top_local
    (H : Subgroup G) (K : Subgroup H) (hK : K < ⊤) :
    Nat.card K < Nat.card H := by
  have hsubset : (K : Set H) ⊂ Set.univ := by
    refine ⟨by intro x hx; simp, ?_⟩
    intro htop
    exact hK.ne <| eq_top_iff.2 (by
      intro x hx
      exact htop (show x ∈ (Set.univ : Set H) by simp))
  -- Proper inclusion of finite sets forces a strict cardinal drop.
  simpa using (Set.toFinite (Set.univ : Set H)).card_lt_card hsubset

/-- Helper for Remark 11-11.1-3: a coatom of an ambient elementary subgroup is strictly smaller in
cardinality than the ambient subgroup. -/
private theorem coatom_card_lt_ambient_local
    (H : Subgroup G) (M : Subgroup H) (hM : IsCoatom M) :
    Nat.card M < Nat.card H := by
  have hsubset : (M : Set H) ⊂ Set.univ := by
    refine ⟨by intro x hx; simp, ?_⟩
    intro htop
    exact hM.1 <| eq_top_iff.2 (by
      intro x hx
      exact htop (show x ∈ (Set.univ : Set H) by simp))
  -- Proper inclusion of finite sets gives the cardinality drop required by strong induction.
  simpa using (Set.toFinite (Set.univ : Set H)).card_lt_card hsubset

/-- Helper for Remark 11-11.1-3: a linear character on `K ≤ H` transports to the image subgroup
`K.map H.subtype`. -/
private def mapped_linear_character_local
    (H : Subgroup G) (K : Subgroup H) (χ : K →* ℂˣ) :
    K.map H.subtype →* ℂˣ :=
  χ.comp (K.equivMapOfInjective H.subtype H.subtype_injective).symm.toMonoidHom

/-- Helper for Remark 11-11.1-3: reindexing along `K ≃ K.map H.subtype` identifies the ambient
pairing with the nested restriction pairing. -/
private theorem mapped_linear_character_pairing_eq_nested_restriction_local
    (φ : classFunctionSubmodule ℂ G)
    (H : Subgroup G) (K : Subgroup H) (χ : K →* ℂˣ) :
    ⟪(mapped_linear_character_local H K χ).toCharacterRing,
        Subgroup.classFunctionRestriction (K.map H.subtype) φ⟫ =
      ⟪χ.toCharacterRing,
        Subgroup.classFunctionRestriction K (Subgroup.classFunctionRestriction H φ)⟫ := by
  classical
  let e : K ≃* K.map H.subtype := K.equivMapOfInjective H.subtype H.subtype_injective
  let nested : K → ℂ := fun y ↦
    (χ.toCharacterRing : K → ℂ) y *
      ((Subgroup.classFunctionRestriction K (Subgroup.classFunctionRestriction H φ) :
          classFunctionSubmodule ℂ K) : K → ℂ) y⁻¹
  let ambient : K.map H.subtype → ℂ := fun y ↦
    (((mapped_linear_character_local H K χ).toCharacterRing :
        K.map H.subtype → ℂ) y) *
      ((Subgroup.classFunctionRestriction (K.map H.subtype) φ :
          classFunctionSubmodule ℂ (K.map H.subtype)) : K.map H.subtype → ℂ) y⁻¹
  -- Rewrite both pairings as normalized sums and reindex along the subgroup equivalence.
  rw [Representation.groupFunctionPairing_eq_card_inv_sum_apply_mul_inv_apply,
    Representation.groupFunctionPairing_eq_card_inv_sum_apply_mul_inv_apply]
  have hcardNat : Nat.card (K.map H.subtype) = Nat.card K :=
    (Nat.card_congr e.toEquiv).symm
  have hcard : ((Nat.card (K.map H.subtype) : ℕ) : ℂ) = (Nat.card K : ℂ) := by
    exact_mod_cast hcardNat
  rw [hcard]
  refine congrArg (fun z : ℂ ↦ (Nat.card K : ℂ)⁻¹ * z) ?_
  change (∑ t : K.map H.subtype, ambient t) = ∑ t : K, nested t
  exact (Fintype.sum_equiv e nested ambient (by
    intro y
    -- After transporting along `e`, both the mapped linear character and the nested restriction
    -- reduce to the original subgroup data.
    dsimp [nested, ambient, mapped_linear_character_local]
    congr 1
    simp [e])).symm

/-- Helper for Remark 11-11.1-3: pairing an integral virtual character with a degree-`1`
character lands in the image of `ℤ`. -/
private theorem pairing_mem_range_int_of_mem_characterRing_with_linear_character_local
    {H : Type*} [Group H] [Finite H] (η : R(H)) (χ : H →* ℂˣ) :
    ⟪χ.toCharacterRing, (η : H → ℂ)⟫ ∈ Set.range (algebraMap ℤ ℂ) := by
  let S : Set (H → ℂ) :=
    { ψ |
        ∃ (X : Type*) (_ : AddCommGroup X) (_ : Module ℂ X)
          (_ : FiniteDimensional ℂ X) (σ : Representation ℂ H X),
          ψ = σ.character }
  have hmul_span :
      ∀ {f g : H → ℂ},
        f ∈ Submodule.span ℤ S →
        g ∈ Submodule.span ℤ S →
        f * g ∈ Submodule.span ℤ S := by
    intro f g hf hg
    have hfg : ∀ g : H → ℂ, g ∈ Submodule.span ℤ S → f * g ∈ Submodule.span ℤ S := by
      induction hf using Submodule.span_induction with
      | mem ψ hψ =>
          have hψ' :
              ∃ (X : Type*) (_ : AddCommGroup X) (_ : Module ℂ X)
                (_ : FiniteDimensional ℂ X) (σ : Representation ℂ H X),
                ψ = σ.character := by
            simpa [S] using hψ
          rcases hψ' with ⟨X, _instXAdd, _instXMod, _instXfd, σ, rfl⟩
          intro g hg
          induction hg using Submodule.span_induction with
          | mem ξ hξ =>
              have hξ' :
                  ∃ (Y : Type*) (_ : AddCommGroup Y) (_ : Module ℂ Y)
                    (_ : FiniteDimensional ℂ Y) (τ : Representation ℂ H Y),
                    ξ = τ.character := by
                simpa [S] using hξ
              rcases hξ' with ⟨Y, _instYAdd, _instYMod, _instYfd, τ, rfl⟩
              let π : Representation ℂ H (TensorProduct ℂ X Y) := σ.tprod τ
              -- Tensor products realize pointwise products of honest characters.
              refine Submodule.subset_span ?_
              refine ⟨TensorProduct ℂ X Y, inferInstance, inferInstance, inferInstance, π, ?_⟩
              change σ.character * τ.character = (σ.tprod τ).character
              exact (Representation.char_tensor (ρ := σ) (σ := τ)).symm
          | zero =>
              have hzero_mul : σ.character * (0 : H → ℂ) = 0 := by
                ext x
                simp
              rw [hzero_mul]
              exact
                (Submodule.zero_mem (Submodule.span ℤ S) : (0 : H → ℂ) ∈ Submodule.span ℤ S)
          | add ξ ζ _ _ hξ hζ =>
              simpa [mul_add] using Submodule.add_mem (Submodule.span ℤ S) hξ hζ
          | smul n ξ _ hξ =>
              have hmul_zsmul : σ.character * (n • ξ) = n • (σ.character * ξ) := by
                ext x
                simp [zsmul_eq_mul, mul_left_comm]
              rw [hmul_zsmul]
              exact Submodule.smul_mem (Submodule.span ℤ S) n hξ
      | zero =>
          intro g hg
          have hzero_mul : (0 : H → ℂ) * g = 0 := by
            ext x
            simp
          rw [hzero_mul]
          exact (Submodule.zero_mem (Submodule.span ℤ S) : (0 : H → ℂ) ∈ Submodule.span ℤ S)
      | add f₁ f₂ _ _ hf₁ hf₂ =>
          intro g hg
          simpa [add_mul] using
            Submodule.add_mem (Submodule.span ℤ S) (hf₁ g hg) (hf₂ g hg)
      | smul n f _ hf =>
          intro g hg
          simpa [zsmul_eq_mul, mul_left_comm, mul_assoc] using
            Submodule.smul_mem (Submodule.span ℤ S) n (hf g hg)
    exact hfg g hg
  have hηspan : (η : H → ℂ) ∈ Submodule.span ℤ S := by
    -- Reduce the bundled character ring element to the `ℤ`-span of honest characters.
    refine Algebra.adjoin_induction ?_ ?_ ?_ ?_ η.2
    · intro ψ hψ
      rcases hψ with ⟨σ, hσfd, _hσirr, rfl⟩
      exact Submodule.subset_span
        ⟨(σ : Type*), inferInstance, inferInstance, hσfd, σ.ρ, rfl⟩
    · intro n
      have htriv :
          (Representation.trivial ℂ H (ULift ℂ)).character = (1 : H → ℂ) := by
        ext x
        simp [Representation.character, Representation.trivial]
      have hmap :
          algebraMap ℤ (H → ℂ) n =
            n • (Representation.trivial ℂ H (ULift ℂ)).character := by
        ext x
        simp [htriv]
      rw [hmap]
      exact
        Submodule.smul_mem (Submodule.span ℤ S) n <|
          Submodule.subset_span
            ⟨ULift ℂ, inferInstance, inferInstance, inferInstance,
              Representation.trivial ℂ H (ULift ℂ), rfl⟩
    · intro f g _ _ hf hg
      exact Submodule.add_mem (Submodule.span ℤ S) hf hg
    · intro f g _ _ hf hg
      exact hmul_span hf hg
  -- Commute the pairing so the `ℤ`-span induction hits the integral character input.
  rw [Representation.groupFunctionPairing_comm]
  have hpair_span :
      ∀ f : H → ℂ, f ∈ Submodule.span ℤ S →
        ⟪f, χ.toCharacterRing⟫ ∈ Set.range (algebraMap ℤ ℂ) := by
    intro f hf
    induction hf using Submodule.span_induction with
    | mem ψ hψ =>
        have hψ' :
            ∃ (X : Type*) (_ : AddCommGroup X) (_ : Module ℂ X)
              (_ : FiniteDimensional ℂ X) (σ : Representation ℂ H X),
              ψ = σ.character := by
          simpa [S] using hψ
        rcases hψ' with ⟨X, _instXAdd, _instXMod, _instXfd, σ, rfl⟩
        have hcard_ne : (Nat.card H : ℂ) ≠ 0 := by
          exact_mod_cast Nat.card_pos.ne'
        letI : Invertible (Nat.card H : ℂ) := invertibleOfNonzero hcard_ne
        have hpair :
            ⟪σ.character, χ.toCharacterRing⟫ =
              Module.finrank ℂ (σ.IntertwiningMap χ.toRepresentation) := by
          simpa [MonoidHom.toCharacterRing_apply] using
            (Representation.groupFunctionPairingOverField_character_eq_finrank_intertwiningMap
              (K := ℂ) σ χ.toRepresentation)
        refine ⟨(Module.finrank ℂ (σ.IntertwiningMap χ.toRepresentation) : ℤ), ?_⟩
        simpa using hpair.symm
    | zero =>
        refine ⟨0, ?_⟩
        simp [Representation.groupFunctionPairingOverField]
    | add ψ ξ _ _ hψ hξ =>
        rcases hψ with ⟨a, ha⟩
        rcases hξ with ⟨b, hb⟩
        refine ⟨a + b, ?_⟩
        calc
          algebraMap ℤ ℂ (a + b) = algebraMap ℤ ℂ a + algebraMap ℤ ℂ b := by simp
          _ = groupFunctionPairingOverField ℂ ψ (χ.toCharacterRing : H → ℂ) +
                groupFunctionPairingOverField ℂ ξ (χ.toCharacterRing : H → ℂ) := by
              rw [ha, hb]
          _ = groupFunctionPairingOverField ℂ (ψ + ξ) (χ.toCharacterRing : H → ℂ) := by
              rw [Representation.groupFunctionPairing_add_left]
    | smul n ψ _ hψ =>
        rcases hψ with ⟨a, ha⟩
        refine ⟨n * a, ?_⟩
        calc
          algebraMap ℤ ℂ (n * a) = (n : ℂ) * algebraMap ℤ ℂ a := by
            simp [map_mul, mul_comm]
          _ = (n : ℂ) * groupFunctionPairingOverField ℂ ψ (χ.toCharacterRing : H → ℂ) := by
              rw [ha]
          _ = groupFunctionPairingOverField ℂ (n • ψ) (χ.toCharacterRing : H → ℂ) := by
              symm
              simpa [zsmul_eq_mul] using
                (Representation.groupFunctionPairing_smul_left
                  (a := (n : ℂ)) (φ := ψ) (ψ := (χ.toCharacterRing : H → ℂ)))
  exact hpair_span (η : H → ℂ) hηspan

/-- Helper for Remark 11-11.1-3: transporting a mapped subgroup coordinate back along the
canonical equivalence identifies it with the ordinary local restriction from `H` to `K`. -/
private theorem mapped_coordinate_transport_eq_local_restriction
    (H : Subgroup G) (K : Subgroup H) (η : R(H)) :
    Subgroup.characterRingTransport
        (K.equivMapOfInjective H.subtype H.subtype_injective)
        ((Subgroup.characterRingRestrictionOfLe (subgroup_chain_map_le_local H K)) η) =
      (K ↾R[ℂ]) η := by
  apply Subtype.ext
  ext k
  -- Both sides evaluate the same ambient character on the underlying subgroup element.
  simp [Subgroup.characterRingTransport_apply, Subgroup.characterRingOverFieldRestrictionOfLe_apply,
    Subgroup.characterRingRestriction_apply, subgroup_chain_map_le_local,
    Subgroup.coe_equivMapOfInjective_apply]

/-- Helper for Remark 11-11.1-3: linear-character pairing is invariant under transporting a
character-ring element back from `K.map H.subtype` to `K`. -/
private theorem linear_character_pairing_transport_eq
    (H : Subgroup G) (K : Subgroup H) (χ : K →* ℂˣ) (η : R(K.map H.subtype)) :
    ⟪((mapped_linear_character_local H K χ).toCharacterRing : K.map H.subtype → ℂ),
        (η : K.map H.subtype → ℂ)⟫ =
      ⟪(χ.toCharacterRing : K → ℂ),
        ((Subgroup.characterRingTransport
          (K.equivMapOfInjective H.subtype H.subtype_injective) η : R(K)) : K → ℂ)⟫ := by
  classical
  let e : K ≃* K.map H.subtype := K.equivMapOfInjective H.subtype H.subtype_injective
  let ambient : K.map H.subtype → ℂ := fun y ↦
    (((mapped_linear_character_local H K χ).toCharacterRing : K.map H.subtype → ℂ) y) *
      (η : K.map H.subtype → ℂ) y⁻¹
  let nested : K → ℂ := fun y ↦
    ((χ.toCharacterRing : K → ℂ) y) *
      (((Subgroup.characterRingTransport e η : R(K)) : K → ℂ) y)⁻¹
  -- Reindex the normalized character-pairing sum along the subgroup equivalence.
  rw [Representation.groupFunctionPairing_eq_card_inv_sum_apply_mul_inv_apply,
    Representation.groupFunctionPairing_eq_card_inv_sum_apply_mul_inv_apply]
  have hcardNat : Nat.card (K.map H.subtype) = Nat.card K :=
    (Nat.card_congr e.toEquiv).symm
  have hcard : ((Nat.card (K.map H.subtype) : ℕ) : ℂ) = (Nat.card K : ℂ) := by
    exact_mod_cast hcardNat
  rw [hcard]
  refine congrArg (fun z : ℂ ↦ (Nat.card K : ℂ)⁻¹ * z) ?_
  change (∑ t : K.map H.subtype, ambient t) = ∑ t : K, nested t
  exact
    (Fintype.sum_equiv e nested ambient fun y ↦ by
      -- Transporting both the character and the local value along `e` returns the original pair.
      dsimp [nested, ambient, mapped_linear_character_local]
      congr 1
      simp [e]).symm

/-- Helper for Remark 11-11.1-3: if a subgroup family over `H` is indexed by all subgroups of
`H`, then the top coordinate already detects whether the ambient class function is integral. -/
private theorem subgroup_restriction_detection_on_elementary_group
    {H : Subgroup G}
    (φ : classFunctionSubmodule ℂ H)
    (hφ : ∀ J : (Finset.univ : Finset (Subgroup H)),
      (J.1.classFunctionRestriction φ : J.1 → ℂ) ∈ R(J.1)) :
    (φ : H → ℂ) ∈ R(H) := by
  let Jtop : (Finset.univ : Finset (Subgroup H)) := ⟨⊤, by simp⟩
  -- The top restriction is literally the original class function.
  simpa [Jtop] using hφ Jtop

/-- Helper for Remark 11-11.1-3: choose the unique integer recording the pairing of a local
character-ring element with the transported degree-`1` character on `K.map H.subtype`. -/
private noncomputable def linear_character_pairing_int_toFun
    (H : Subgroup G) (K : Subgroup H) (χ : K →* ℂˣ) :
    R(K.map H.subtype) → ℤ :=
  fun η ↦ Classical.choose <|
    pairing_mem_range_int_of_mem_characterRing_with_linear_character_local
      (η := η) (χ := mapped_linear_character_local H K χ)

/-- Helper for Remark 11-11.1-3: the chosen integer witness recovers the corresponding complex
linear-character pairing. -/
private theorem linear_character_pairing_int_toFun_spec
    (H : Subgroup G) (K : Subgroup H) (χ : K →* ℂˣ) (η : R(K.map H.subtype)) :
    algebraMap ℤ ℂ (linear_character_pairing_int_toFun H K χ η) =
      ⟪((mapped_linear_character_local H K χ).toCharacterRing : K.map H.subtype → ℂ),
          (η : K.map H.subtype → ℂ)⟫ := by
  -- Unpack the chosen witness from the integrality theorem above.
  exact Classical.choose_spec <|
    pairing_mem_range_int_of_mem_characterRing_with_linear_character_local
      (η := η) (χ := mapped_linear_character_local H K χ)

/-- Helper for Remark 11-11.1-3: the integer witness for linear-character pairing is additive. -/
private theorem linear_character_pairing_int_toFun_map_add
    (H : Subgroup G) (K : Subgroup H) (χ : K →* ℂˣ) (η θ : R(K.map H.subtype)) :
    linear_character_pairing_int_toFun H K χ (η + θ) =
      linear_character_pairing_int_toFun H K χ η +
        linear_character_pairing_int_toFun H K χ θ := by
  apply Int.cast_injective
  -- Compare both integers after casting to `ℂ`, where the pairing is manifestly additive.
  calc
    algebraMap ℤ ℂ (linear_character_pairing_int_toFun H K χ (η + θ)) =
        ⟪((mapped_linear_character_local H K χ).toCharacterRing : K.map H.subtype → ℂ),
            ((η + θ : R(K.map H.subtype)) : K.map H.subtype → ℂ)⟫ := by
          exact linear_character_pairing_int_toFun_spec H K χ (η + θ)
    _ = ⟪((mapped_linear_character_local H K χ).toCharacterRing : K.map H.subtype → ℂ),
            (η : K.map H.subtype → ℂ)⟫ +
          ⟪((mapped_linear_character_local H K χ).toCharacterRing : K.map H.subtype → ℂ),
            (θ : K.map H.subtype → ℂ)⟫ := by
          exact Representation.groupFunctionPairing_add_right
            (((mapped_linear_character_local H K χ).toCharacterRing : R(K.map H.subtype)) :
              K.map H.subtype → ℂ)
            (η : K.map H.subtype → ℂ)
            (θ : K.map H.subtype → ℂ)
    _ = algebraMap ℤ ℂ (linear_character_pairing_int_toFun H K χ η) +
          algebraMap ℤ ℂ (linear_character_pairing_int_toFun H K χ θ) := by
          rw [linear_character_pairing_int_toFun_spec H K χ η,
            linear_character_pairing_int_toFun_spec H K χ θ]
    _ = algebraMap ℤ ℂ
          (linear_character_pairing_int_toFun H K χ η +
            linear_character_pairing_int_toFun H K χ θ) := by
          simp

/-- Helper for Remark 11-11.1-3: the integer witness for linear-character pairing is `ℤ`-linear.
-/
private theorem linear_character_pairing_int_toFun_map_zsmul
    (H : Subgroup G) (K : Subgroup H) (χ : K →* ℂˣ) (n : ℤ) (η : R(K.map H.subtype)) :
    linear_character_pairing_int_toFun H K χ (n • η) =
      n * linear_character_pairing_int_toFun H K χ η := by
  apply Int.cast_injective
  -- After casting to `ℂ`, this is exactly right-linearity of the pairing.
  calc
    algebraMap ℤ ℂ (linear_character_pairing_int_toFun H K χ (n • η)) =
        ⟪((mapped_linear_character_local H K χ).toCharacterRing : K.map H.subtype → ℂ),
            ((n • η : R(K.map H.subtype)) : K.map H.subtype → ℂ)⟫ := by
          exact linear_character_pairing_int_toFun_spec H K χ (n • η)
    _ = (n : ℂ) *
          ⟪((mapped_linear_character_local H K χ).toCharacterRing : K.map H.subtype → ℂ),
              (η : K.map H.subtype → ℂ)⟫ := by
          simpa [zsmul_eq_mul] using
            (Representation.groupFunctionPairing_smul_right
              (a := (n : ℂ))
              (φ := (((mapped_linear_character_local H K χ).toCharacterRing :
                R(K.map H.subtype)) : K.map H.subtype → ℂ))
              (ψ := (η : K.map H.subtype → ℂ))).symm
    _ = (n : ℂ) * algebraMap ℤ ℂ (linear_character_pairing_int_toFun H K χ η) := by
          rw [linear_character_pairing_int_toFun_spec H K χ η]
    _ = algebraMap ℤ ℂ (n * linear_character_pairing_int_toFun H K χ η) := by
          simp [Int.cast_mul]

/-- Helper for Remark 11-11.1-3: the transported degree-`1` pairing is represented by a
`ℤ`-linear functional on the local character ring. -/
private noncomputable def linear_character_pairing_int
    (H : Subgroup G) (K : Subgroup H) (χ : K →* ℂˣ) :
    R(K.map H.subtype) →ₗ[ℤ] ℤ :=
  { toFun := linear_character_pairing_int_toFun H K χ
    map_add' := linear_character_pairing_int_toFun_map_add H K χ
    map_smul' := linear_character_pairing_int_toFun_map_zsmul H K χ }

/-- Helper for Remark 11-11.1-3: the integer-valued pairing linear map casts back to the original
complex pairing. -/
private theorem linear_character_pairing_int_spec
    (H : Subgroup G) (K : Subgroup H) (χ : K →* ℂˣ) (η : R(K.map H.subtype)) :
    algebraMap ℤ ℂ (linear_character_pairing_int H K χ η) =
      ⟪((mapped_linear_character_local H K χ).toCharacterRing : K.map H.subtype → ℂ),
          (η : K.map H.subtype → ℂ)⟫ := by
  exact linear_character_pairing_int_toFun_spec H K χ η

/-- Helper for Remark 11-11.1-3: after transporting a `K.map H.subtype` coordinate back to `K`,
the resulting local pairing is still the integer-valued ambient pairing. -/
private theorem subgroup_linear_character_pairing_int_transport_eq
    (H : Subgroup G) (K : Subgroup H) (χ : K →* ℂˣ) (η : R(K.map H.subtype)) :
    ⟪(χ.toCharacterRing : K → ℂ),
        ((Subgroup.characterRingTransport
          (K.equivMapOfInjective H.subtype H.subtype_injective) η : R(K)) : K → ℂ)⟫ =
      algebraMap ℤ ℂ (linear_character_pairing_int H K χ η) := by
  -- First rewrite the transported pairing back to the ambient `K.map H.subtype` coordinate,
  -- then read off the chosen integer witness for that pairing.
  calc
    ⟪(χ.toCharacterRing : K → ℂ),
        ((Subgroup.characterRingTransport
          (K.equivMapOfInjective H.subtype H.subtype_injective) η : R(K)) : K → ℂ)⟫ =
      ⟪((mapped_linear_character_local H K χ).toCharacterRing : K.map H.subtype → ℂ),
          (η : K.map H.subtype → ℂ)⟫ := by
        symm
        exact linear_character_pairing_transport_eq H K χ η
    _ = algebraMap ℤ ℂ (linear_character_pairing_int H K χ η) := by
        symm
        exact linear_character_pairing_int_spec H K χ η

/-- Helper for Remark 11-11.1-3: when `J ≤ M ≤ H`, the ambient integer pairing computed in `H`
agrees with the same pairing computed in the smaller ambient subgroup `M` after transporting the
coordinate back along the canonical subgroup-chain equivalence. -/
private theorem linear_character_pairing_int_subgroupOf_eq
    (H : Subgroup G) (M : Subgroup H) (J : Subgroup M) (α : J →* ℂˣ)
    (η : R((J.map M.subtype).map H.subtype)) :
    linear_character_pairing_int H (J.map M.subtype) (mapped_linear_character_local M J α) η =
      linear_character_pairing_int M J α
        (Subgroup.characterRingTransport
          ((J.map M.subtype).equivMapOfInjective H.subtype H.subtype_injective) η) := by
  apply Int.cast_injective
  -- First rewrite the ambient pairing in `H` as the transported pairing on `J.map M.subtype`.
  calc
    algebraMap ℤ ℂ
        (linear_character_pairing_int H (J.map M.subtype) (mapped_linear_character_local M J α) η) =
      ⟪((mapped_linear_character_local H (J.map M.subtype)
            (mapped_linear_character_local M J α)).toCharacterRing :
          (J.map M.subtype).map H.subtype → ℂ),
          (η : (J.map M.subtype).map H.subtype → ℂ)⟫ := by
            exact
              linear_character_pairing_int_spec H (J.map M.subtype)
                (mapped_linear_character_local M J α) η
    _ =
      ⟪((mapped_linear_character_local M J α).toCharacterRing : J.map M.subtype → ℂ),
          ((Subgroup.characterRingTransport
              ((J.map M.subtype).equivMapOfInjective H.subtype H.subtype_injective) η :
                R(J.map M.subtype)) : J.map M.subtype → ℂ)⟫ := by
            exact
              linear_character_pairing_transport_eq H (J.map M.subtype)
                (mapped_linear_character_local M J α) η
    _ =
      algebraMap ℤ ℂ
        (linear_character_pairing_int M J α
          (Subgroup.characterRingTransport
            ((J.map M.subtype).equivMapOfInjective H.subtype H.subtype_injective) η)) := by
            symm
            exact
              linear_character_pairing_int_spec M J α
                (Subgroup.characterRingTransport
                  ((J.map M.subtype).equivMapOfInjective H.subtype H.subtype_injective) η)

/-- Helper for Remark 11-11.1-3: divisibility of the smaller-ambient pairing transports unchanged
across the subgroup chain `J ≤ M ≤ H`. -/
private theorem subgroup_chain_pairing_divisible_transport_local
    (H : Subgroup G) (M : Subgroup H) (J : Subgroup M) (α : J →* ℂˣ)
    (η : R((J.map M.subtype).map H.subtype)) {n : ℤ}
    (hdiv :
      ∃ c : ℤ,
        linear_character_pairing_int M J α
          (Subgroup.characterRingTransport
            ((J.map M.subtype).equivMapOfInjective H.subtype H.subtype_injective) η) =
          n * c) :
    ∃ c : ℤ,
      linear_character_pairing_int H (J.map M.subtype) (mapped_linear_character_local M J α) η =
        n * c := by
  rcases hdiv with ⟨c, hc⟩
  refine ⟨c, ?_⟩
  -- Rewrite the ambient pairing as the transported smaller-ambient pairing, then reuse the same
  -- integer witness.
  calc
    linear_character_pairing_int H (J.map M.subtype) (mapped_linear_character_local M J α) η =
        linear_character_pairing_int M J α
          (Subgroup.characterRingTransport
            ((J.map M.subtype).equivMapOfInjective H.subtype H.subtype_injective) η) := by
              exact linear_character_pairing_int_subgroupOf_eq H M J α η
    _ = n * c := hc

/-- Helper for Remark 11-11.1-3: transporting the ambient restriction-defect identity from `X`
to the full subgroup family of a fixed `H ∈ X` produces the source-faithful local defect
equation. -/
private theorem transported_subgroup_family_defect_eq_zsmul
    (X : Finset (Subgroup G))
    (hXelem : ∀ H : Subgroup G, H ∈ X ↔ IsElementary H)
    {x : (H : X) → R(H.1)} {t : elementary_coherence_target X hXelem} {n : ℤ}
    (hdx : elementary_coherence_defect X hXelem x = n • t)
    (H : X) :
    let XH : Finset (Subgroup H.1) := Finset.univ
    let ψH : (J : XH) → R(J.1) := fun J ↦
      Subgroup.characterRingTransport
        (J.1.equivMapOfInjective H.1.subtype H.1.subtype_injective)
        (x ⟨J.1.map H.1.subtype,
          (hXelem (J.1.map H.1.subtype)).2 <|
            isElementary_of_mulEquiv_local
              (J.1.equivMapOfInjective H.1.subtype H.1.subtype_injective)
              (subgroup_isElementary_of_isElementary_local J.1 ((hXelem H.1).1 H.2))⟩)
    let δH : (J : XH) → R(J.1) := fun J ↦
      let JX : X := ⟨J.1.map H.1.subtype,
        (hXelem (J.1.map H.1.subtype)).2 <|
          isElementary_of_mulEquiv_local
            (J.1.equivMapOfInjective H.1.subtype H.1.subtype_injective)
            (subgroup_isElementary_of_isElementary_local J.1 ((hXelem H.1).1 H.2))⟩
      let pJ : elementary_restriction_relation X := ⟨(H, JX), subgroup_chain_map_le_local H.1 J.1⟩
      Subgroup.characterRingTransport
        (J.1.equivMapOfInjective H.1.subtype H.1.subtype_injective)
        (t.1 pJ)
    ((Representation.characterRingRestriction XH).toLinearMap (x H)) - ψH = n • δH := by
  classical
  dsimp
  ext J j
  let JX : X := ⟨J.1.map H.1.subtype,
    (hXelem (J.1.map H.1.subtype)).2 <|
      isElementary_of_mulEquiv_local
        (J.1.equivMapOfInjective H.1.subtype H.1.subtype_injective)
        (subgroup_isElementary_of_isElementary_local J.1 ((hXelem H.1).1 H.2))⟩
  let pJ : elementary_restriction_relation X := ⟨(H, JX), subgroup_chain_map_le_local H.1 J.1⟩
  have hp :
      ((Subgroup.characterRingRestrictionOfLe (subgroup_chain_map_le_local H.1 J.1)) (x H) :
          R(JX.1)) - x JX = n • t.1 pJ := by
    have hp' := congrFun (congrArg Prod.fst hdx) pJ
    -- The global first defect block specializes to the `H ⟶ JX` restriction equation.
    simpa [elementary_coherence_defect, pJ, JX] using hp'
  have hp_eval := congrArg
    (fun ζ : R(JX.1) ↦
      ((ζ : JX.1 → ℂ) ((J.1.equivMapOfInjective H.1.subtype H.1.subtype_injective) j))) hp
  -- Evaluating at the subgroup equivalence turns the ambient coordinate identity into the local
  -- transported family equation on `J`.
  simpa [JX, pJ, Representation.characterRingRestriction_apply, Pi.sub_apply, Pi.smul_apply,
    Subgroup.characterRingTransport_apply, Subgroup.characterRingOverFieldRestrictionOfLe_apply,
    Subgroup.coe_equivMapOfInjective_apply, zsmul_eq_mul] using hp_eval

/-- Helper for Remark 11-11.1-3: once the local defect identity is written on the subgroup family
of `H`, the residual projector turns it into a pure `n`-multiple identity. -/
private theorem local_residual_projector_eq_neg_zsmul
    {H0 : Type*} [Group H0] [Finite H0]
    (XH : Finset (Subgroup H0))
    (sH : ((J : XH) → R(J.1)) →ₗ[ℤ] R(H0))
    (hsH : Function.LeftInverse sH (Representation.characterRingRestriction XH).toLinearMap)
    {ξ : R(H0)} {ψ δ : (J : XH) → R(J.1)} {n : ℤ}
    (hξ : ((Representation.characterRingRestriction XH).toLinearMap ξ) - ψ = n • δ) :
    let fH : R(H0) →ₗ[ℤ] ((J : XH) → R(J.1)) :=
      (Representation.characterRingRestriction XH).toLinearMap
    let rH : ((J : XH) → R(J.1)) →ₗ[ℤ] ((J : XH) → R(J.1)) :=
      LinearMap.id - fH.comp sH
    rH ψ = (-n) • rH δ := by
  dsimp
  let fH : R(H0) →ₗ[ℤ] ((J : XH) → R(J.1)) := (Representation.characterRingRestriction XH).toLinearMap
  let rH : ((J : XH) → R(J.1)) →ₗ[ℤ] ((J : XH) → R(J.1)) := LinearMap.id - fH.comp sH
  have hrξ : rH (fH ξ) = 0 := by
    -- The residual projector kills the actual image of the local restriction-family map.
    change fH ξ - fH (sH (fH ξ)) = 0
    rw [hsH ξ]
    simp
  have hneg : -rH ψ = n • rH δ := by
    -- Apply the projector to the transported defect equation and use `rH ∘ fH = 0`.
    simpa [rH, LinearMap.map_sub, LinearMap.map_zsmul, hrξ] using congrArg rH hξ
  have hfinal := congrArg Neg.neg hneg
  simpa [zsmul_eq_mul, mul_comm, mul_left_comm, mul_assoc] using hfinal

/-- Helper for Remark 11-11.1-3: applying the local residual projector to the transported subgroup
family keeps the image term `fH (sH ψ)` explicit, and the remaining error is an `n`-multiple in
the `K`-pairing. -/
private theorem local_residual_pairing_decomposition_of_defect_multiple
    {H0 : Type*} [Group H0] [Finite H0]
    (XH : Finset (Subgroup H0))
    (sH : ((J : XH) → R(J.1)) →ₗ[ℤ] R(H0))
    (hsH : Function.LeftInverse sH (Representation.characterRingRestriction XH).toLinearMap)
    {ψ δ : (J : XH) → R(J.1)} {n : ℤ}
    (htransported :
      let fH : R(H0) →ₗ[ℤ] ((J : XH) → R(J.1)) :=
        (Representation.characterRingRestriction XH).toLinearMap
      fH (sH ψ) - ψ = n •
        (((LinearMap.id : ((J : XH) → R(J.1)) →ₗ[ℤ] ((J : XH) → R(J.1))) -
          ((Representation.characterRingRestriction XH).toLinearMap).comp sH) δ))
    (K : XH) (χ : K.1 →* ℂˣ) :
    ∃ m : ℤ,
      ⟪(χ.toCharacterRing : K.1 → ℂ), (ψ K : K.1 → ℂ)⟫ =
        ⟪(χ.toCharacterRing : K.1 → ℂ),
            (((Representation.characterRingRestriction XH) (sH ψ) K : R(K.1)) :
              K.1 → ℂ)⟫ +
          algebraMap ℤ ℂ (n * m) := by
  let fH : R(H0) →ₗ[ℤ] ((J : XH) → R(J.1)) :=
    (Representation.characterRingRestriction XH).toLinearMap
  let rH : ((J : XH) → R(J.1)) →ₗ[ℤ] ((J : XH) → R(J.1)) :=
    LinearMap.id - fH.comp sH
  have hresidual : ψ - fH (sH ψ) = n • rH δ := by
    -- Route correction: keep the local-image term explicit instead of trying to identify `ψ K`
    -- directly with the pure residual coordinate.
    simpa [fH, rH, Pi.sub_apply, LinearMap.sub_apply, LinearMap.comp_apply,
      sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using htransported
  let pairK : R(K.1) →ₗ[ℤ] ℂ :=
    { toFun := fun η ↦ ⟪(χ.toCharacterRing : K.1 → ℂ), (η : K.1 → ℂ)⟫
      map_add' := by
        intro η θ
        exact Representation.groupFunctionPairing_add_right
          (χ.toCharacterRing : K.1 → ℂ) (η : K.1 → ℂ) (θ : K.1 → ℂ)
      map_smul' := by
        intro a η
        simpa [zsmul_eq_mul] using
          (Representation.groupFunctionPairing_smul_right
            (a := (a : ℂ))
            (φ := (χ.toCharacterRing : K.1 → ℂ))
            (ψ := (η : K.1 → ℂ))).symm }
  rcases pairing_mem_range_int_of_mem_characterRing_with_linear_character_local
      (η := rH δ K) (χ := χ) with ⟨b, hb⟩
  have hpair_sub :
      pairK (ψ K - fH (sH ψ) K) = algebraMap ℤ ℂ (n * b) := by
    have hcoord := congrArg (fun ζ : (J : XH) → R(J.1) ↦ ζ K) hresidual
    calc
      pairK (ψ K - fH (sH ψ) K) = pairK (n • rH δ K) := by
        simpa [Pi.smul_apply] using congrArg pairK hcoord
      _ = algebraMap ℤ ℂ (n * b) := by
        rw [LinearMap.map_smul]
        simp [hb, Int.cast_mul]
  refine ⟨-b, ?_⟩
  have hpair_eq :
      ⟪(χ.toCharacterRing : K.1 → ℂ), (ψ K : K.1 → ℂ)⟫ -
          ⟪(χ.toCharacterRing : K.1 → ℂ),
              (((Representation.characterRingRestriction XH) (sH ψ) K : R(K.1)) :
                K.1 → ℂ)⟫ =
        algebraMap ℤ ℂ (n * b) := by
    simpa [pairK, fH, Representation.characterRingRestriction_apply, sub_eq_add_neg,
      map_sub] using hpair_sub
  -- Move the explicit image term to the right-hand side; only the `n`-multiple remains.
  calc
    ⟪(χ.toCharacterRing : K.1 → ℂ), (ψ K : K.1 → ℂ)⟫ =
        ⟪(χ.toCharacterRing : K.1 → ℂ),
            (((Representation.characterRingRestriction XH) (sH ψ) K : R(K.1)) :
              K.1 → ℂ)⟫ +
          algebraMap ℤ ℂ (n * b) := by
            exact eq_add_of_sub_eq hpair_eq
    _ =
        ⟪(χ.toCharacterRing : K.1 → ℂ),
            (((Representation.characterRingRestriction XH) (sH ψ) K : R(K.1)) :
              K.1 → ℂ)⟫ +
          algebraMap ℤ ℂ (n * (-(-b))) := by
            simp
    _ =
        ⟪(χ.toCharacterRing : K.1 → ℂ),
            (((Representation.characterRingRestriction XH) (sH ψ) K : R(K.1)) :
              K.1 → ℂ)⟫ +
          algebraMap ℤ ℂ (n * (-b)) := by
            simp

/-- Helper for Remark 11-11.1-3: the remaining arithmetic step is to show that the residual
`K`-coordinate pairing extracted from the defect identity is divisible by `n` in `ℤ`. -/
private theorem top_local_image_restriction_eq_coordinate
    {H0 : Type*} [Group H0] [Finite H0]
    (ξ : R(H0)) (J : Subgroup H0) :
    let XH : Finset (Subgroup H0) := Finset.univ
    let J0 : XH := ⟨J, by simp [XH]⟩
    ((Representation.characterRingRestriction XH) ξ J0 : R(J)) =
      Subgroup.characterRingRestrictionOfLe (show J ≤ ⊤ from le_top) ξ := by
  classical
  dsimp
  -- Both local descriptions are the ordinary restriction of `ξ` from `H0` to `J`.
  apply Subtype.ext
  ext j
  simp [Representation.characterRingRestriction_apply,
    Subgroup.characterRingOverFieldRestrictionOfLe_apply]

/-- Helper for Remark 11-11.1-3: in the irreducible-character basis of a finite group, the
coordinates are the corresponding Frobenius character pairings. -/
private theorem repr_irreducible_character_basis_eq_pairing_local
    {H : Type}
    [Group H] [Finite H]
    {ι : Type*}
    (π : ι → FDRep ℂ H)
    (hπ_pairwise : CategoryTheory.PairwiseNonisomorphic π)
    (hπ_complete : IsCompleteIrreducibleFamily π)
    [Fintype ι]
    (x : classFunctionSubmodule ℂ H) (i : ι) :
    (irreducibleCharacters_basis_of_classFunctionSubspace_of_complete_family
        π hπ_pairwise hπ_complete).repr x i =
      Representation.groupFunctionPairingOverField ℂ (x : H → ℂ) (π i).character := by
  classical
  let _ : Fintype H := Fintype.ofFinite H
  let _ : NeZero (Nat.card H : ℂ) := ⟨by
    exact_mod_cast Nat.card_pos.ne'⟩
  let b := irreducibleCharacters_basis_of_classFunctionSubspace_of_complete_family
    π hπ_pairwise hπ_complete
  let coordLinear : classFunctionSubmodule ℂ H →ₗ[ℂ] ℂ :=
    { toFun := fun y ↦ b.repr y i
      map_add' := by
        intro y z
        simp
      map_smul' := by
        intro a y
        simp }
  let pairLinear : classFunctionSubmodule ℂ H →ₗ[ℂ] ℂ :=
    { toFun := fun y ↦
        Representation.groupFunctionPairingOverField ℂ (y : H → ℂ) (π i).character
      map_add' := by
        intro y z
        simpa using Representation.groupFunctionPairing_add_left
          (y : H → ℂ) (z : H → ℂ) (π i).character
      map_smul' := by
        intro a y
        simpa using Representation.groupFunctionPairing_smul_left
          a (y : H → ℂ) (π i).character }
  have hmaps : coordLinear = pairLinear := by
    -- Compare the coordinate functional and the pairing functional on each irreducible basis
    -- vector.
    apply b.ext
    intro j
    have hcoord_j : coordLinear (b j) = if i = j then 1 else 0 := by
      simpa [eq_comm] using
        (show coordLinear (b j) = if j = i then 1 else 0 by
          simp [coordLinear, Module.Basis.repr_self, Finsupp.single_apply])
    have hpair_j : pairLinear (b j) = if i = j then 1 else 0 := by
      by_cases hij : i = j
      · subst hij
        letI : CategoryTheory.Simple (π i) := hπ_complete.isSimple i
        have hself_iso : Nonempty (π i ≅ π i) := ⟨CategoryTheory.Iso.refl _⟩
        calc
          pairLinear (b i) =
              Representation.groupFunctionPairingOverField ℂ
                (π i).character (π i).character := by
            simp [pairLinear, b,
              irreducibleCharacters_basis_of_classFunctionSubspace_of_complete_family_apply]
          _ = 1 := by
            simpa [Representation.groupFunctionPairing_eq_card_inv_sum_apply_mul_inv_apply,
              hself_iso] using
              (FDRep.char_orthonormal (π i) (π i))
          _ = if i = i then 1 else 0 := by simp
      · have hji : j ≠ i := fun h ↦ hij h.symm
        letI : CategoryTheory.Simple (π j) := hπ_complete.isSimple j
        letI : CategoryTheory.Simple (π i) := hπ_complete.isSimple i
        have hnot : ¬ Nonempty (π j ≅ π i) := hπ_pairwise hji
        calc
          pairLinear (b j) =
              Representation.groupFunctionPairingOverField ℂ
                (π j).character (π i).character := by
            simp [pairLinear, b,
              irreducibleCharacters_basis_of_classFunctionSubspace_of_complete_family_apply]
          _ = 0 := by
            simpa [Representation.groupFunctionPairing_eq_card_inv_sum_apply_mul_inv_apply,
              hnot] using
              (FDRep.char_orthonormal (π j) (π i))
          _ = if i = j then 1 else 0 := by simp [hij]
    exact hcoord_j.trans hpair_j.symm
  -- Apply the functional identity to the chosen class function.
  have hmaps_apply := congrArg
    (fun f : classFunctionSubmodule ℂ H →ₗ[ℂ] ℂ ↦ f x) hmaps
  simpa [coordLinear, pairLinear] using hmaps_apply

/-- Helper for Remark 11-11.1-3: Frobenius reciprocity rewrites the pairing of an induced linear
character with a class function as the pairing on the subgroup restriction. -/
private theorem groupFunctionPairing_induced_linearCharacter_eq_restriction
    {H : Type} [Group H] [Finite H]
    (K : Subgroup H) (α : K →* ℂˣ) (x : classFunctionSubmodule ℂ H) :
    ⟪Ind[K](α.toRepresentation.character), (x : H → ℂ)⟫ =
      ⟪α.toCharacterRing, Subgroup.classFunctionRestriction K x⟫ := by
  classical
  let _ : Fintype H := Fintype.ofFinite H
  let _ : Fintype K := Fintype.ofFinite K
  let _ : NeZero (Nat.card H : ℂ) := ⟨by
    exact_mod_cast Nat.card_pos.ne'⟩
  let _ : NeZero (Nat.card K : ℂ) := ⟨by
    exact_mod_cast Nat.card_pos.ne'⟩
  let _ : Invertible (Nat.card H : ℂ) := invertibleOfNonzero <| by
    simpa using (NeZero.ne (Nat.card H : ℂ))
  let _ : Invertible (Nat.card K : ℂ) := invertibleOfNonzero <| by
    simpa using (NeZero.ne (Nat.card K : ℂ))
  obtain ⟨ι, _, π, hπ_pairwise, hπ_complete⟩ :=
    FDRep.exists_complete_pairwise_nonisomorphic_simple_family (k := ℂ) (G := H)
  let b := irreducibleCharacters_basis_of_classFunctionSubspace_of_complete_family
    π hπ_pairwise hπ_complete
  let inducedPairing : classFunctionSubmodule ℂ H →ₗ[ℂ] ℂ :=
    { toFun := fun y ↦ ⟪Ind[K](α.toRepresentation.character), (y : H → ℂ)⟫
      map_add' := by
        intro y z
        simpa using Representation.groupFunctionPairing_add_right
          (Ind[K](α.toRepresentation.character)) (y : H → ℂ) (z : H → ℂ)
      map_smul' := by
        intro a y
        simpa using Representation.groupFunctionPairing_smul_right
          a (Ind[K](α.toRepresentation.character)) (y : H → ℂ) }
  let restrictedPairing : classFunctionSubmodule ℂ H →ₗ[ℂ] ℂ :=
    { toFun := fun y ↦ ⟪α.toCharacterRing, Subgroup.classFunctionRestriction K y⟫
      map_add' := by
        intro y z
        simp [Representation.groupFunctionPairing_add_right]
      map_smul' := by
        intro a y
        simp [Representation.groupFunctionPairing_smul_right] }
  have hmaps : inducedPairing = restrictedPairing := by
    -- It suffices to compare both functionals on the irreducible-character basis of `H`.
    apply b.ext
    intro i
    have hind :
        Ind[K](α.toRepresentation.character) =
          (Representation.ind K.subtype α.toRepresentation).character := by
      simpa using
        (Subgroup.inducedClassFunction_eq_character_ind (H := K) (θ := α.toRepresentation))
    have hrestrict :
        ((Subgroup.classFunctionRestriction K (b i) : classFunctionSubmodule ℂ K) : K → ℂ) =
          Representation.character ((π i).ρ.comp K.subtype) := by
      ext k
      simp [b, irreducibleCharacters_basis_of_classFunctionSubspace_of_complete_family_apply,
        Subgroup.classFunctionRestriction_apply, FDRep.character, Representation.character]
    calc
      inducedPairing (b i) =
          ⟪(Representation.ind K.subtype α.toRepresentation).character, (π i).character⟫ := by
            simp [inducedPairing, hind, b,
              irreducibleCharacters_basis_of_classFunctionSubspace_of_complete_family_apply]
      _ = ⟪α.toRepresentation.character, Representation.character ((π i).ρ.comp K.subtype)⟫ := by
            simpa using
              (groupFunctionPairing_character_comp_eq_character_ind_bridge
                (α := K.subtype) (E := (π i).ρ) (θ := α.toRepresentation)).symm
      _ = restrictedPairing (b i) := by
            simp [restrictedPairing, hrestrict]
  -- Evaluate the functional identity at `x`.
  have hmaps_apply := congrArg
    (fun f : classFunctionSubmodule ℂ H →ₗ[ℂ] ℂ ↦ f x) hmaps
  simpa [inducedPairing, restrictedPairing] using hmaps_apply

/-- Helper for Remark 11-11.1-3: the explicit top-local coordinate pairing rewrites to the
ambient induced pairing on the chosen elementary subgroup. -/
private theorem top_local_coordinate_pairing_eq_induced_pairing
    {H0 : Type*} [Group H0] [Finite H0]
    (sH : ((J : (Finset.univ : Finset (Subgroup H0))) → R(J.1)) →ₗ[ℤ] R(H0))
    (ψH : (J : (Finset.univ : Finset (Subgroup H0))) → R(J.1))
    (K : Subgroup H0) (χ : K →* ℂˣ) :
    let XH : Finset (Subgroup H0) := Finset.univ
    let K0 : XH := ⟨K, by simp [XH]⟩
    ⟪(χ.toCharacterRing : K → ℂ),
        (((Representation.characterRingRestriction XH) (sH ψH) K0 : R(K)) : K → ℂ)⟫ =
      ⟪Ind[K](χ.toRepresentation.character), (((sH ψH : R(H0)) : H0 → ℂ))⟫ := by
  classical
  dsimp
  let ξH : R(H0) := sH ψH
  let ξcf : classFunctionSubmodule ℂ H0 :=
    ⟨(ξH : H0 → ℂ), by
      -- The chosen local image already lies in the character ring, hence is a class function.
      rw [mem_classFunctionSubmodule_iff]
      exact isClassFunction_of_mem_characterRingOverField _ ξH.property⟩
  have hrestrict :
      ((Representation.characterRingRestriction (Finset.univ : Finset (Subgroup H0))) ξH
          ⟨K, by simp⟩ : R(K)) =
        Subgroup.characterRingRestrictionOfLe (show K ≤ ⊤ from le_top) ξH := by
    -- On the universal subgroup family, the `K`-coordinate is the ordinary restriction to `K`.
    exact top_local_image_restriction_eq_coordinate ξH K
  -- Rewrite the explicit coordinate as a subgroup restriction, then apply Frobenius reciprocity.
  rw [hrestrict]
  simpa [ξH, ξcf] using
    (groupFunctionPairing_induced_linearCharacter_eq_restriction
      (K := K) (α := χ) (x := ξcf)).symm

/-- Helper for Remark 11-11.1-3: on an elementary ambient group, subtracting the index copy of
the trivial character moves an induced linear character into LinearRepresentations_Serre_1977's augmentation subgroup
`R₀'`. -/
private theorem induced_linearCharacter_sub_index_smul_one_mem_augmentation_of_isElementary
    {H0 : Type*} [Group H0] [Finite H0]
    (hH0 : IsElementary H0) (K : Subgroup H0) (χ : K →* ℂˣ) :
    (Subgroup.characterRingInduction K χ.toCharacterRing - (K.index : ℤ) • (1 : R(H0))) ∈
      R₀'(H0) := by
  have hzero :
      (((Subgroup.characterRingInduction K χ.toCharacterRing - (K.index : ℤ) • (1 : R(H0)) :
          R(H0)) : H0 → ℂ) 1) = 0 := by
    -- The induced linear character has degree `K.index`, so the augmentation theorem applies to
    -- the difference with the matching trivial summand.
    simp [Subgroup.characterRingInduction_apply,
      Subgroup.inducedClassFunction_one_eq_index_mul_value]
  -- Route correction: package the Chapter 10 zero-at-identity step explicitly so the remaining
  -- blocker is only the pairing divisibility on `R₀'`.
  exact
    character_mem_elementaryLinearCharacterAugmentationSpan_of_apply_one_eq_zero_of_isElementary
      (G := H0) hH0 hzero

/-- Helper for Remark 11-11.1-3: on an elementary ambient group, every induced degree-`1`
subgroup character already belongs to LinearRepresentations_Serre_1977's span `R'`. -/
private theorem induced_linearCharacter_mem_elementaryLinearCharacterSpan_of_subgroup_of_isElementary_local
    {H0 : Type*} [Group H0] [Finite H0]
    (K : Subgroup H0) (χ : K →* ℂˣ) (hH0 : IsElementary H0) :
    Subgroup.characterRingInduction K χ.toCharacterRing ∈ R'(H0) := by
  have htriv :
      Subgroup.characterRingInduction K (1 : R(K)) ∈ R'(H0) :=
    Subgroup.induced_trivial_mem_elementaryLinearCharacterSpan_of_subgroup_of_isElementary K hH0
  have hK : IsElementary K := subgroup_isElementary_of_isElementary_local K hH0
  have haugK :
      (χ.toCharacterRing - 1 : R(K)) ∈ R₀'(K) :=
    linearCharacter_difference_mem_elementaryLinearCharacterAugmentationSpan_of_isElementary
      (G := K) hK χ
  have haug_map :
      Subgroup.characterRingInduction K (χ.toCharacterRing - 1) ∈
        Submodule.map (Subgroup.characterRingInduction K) (R₀'(K)) := by
    -- Package the subgroup augmentation piece as an element of the mapped augmentation span.
    exact ⟨χ.toCharacterRing - 1, haugK, rfl⟩
  have haugH0 :
      Subgroup.characterRingInduction K (χ.toCharacterRing - 1) ∈ R₀'(H0) :=
    Subgroup.map_elementaryLinearCharacterAugmentationSpan K haug_map
  have haugH0' :
      Subgroup.characterRingInduction K (χ.toCharacterRing - 1) ∈ R'(H0) := by
    -- The augmentation subgroup is the right summand of LinearRepresentations_Serre_1977's span `R'`.
    rw [elementaryLinearCharacterSpan]
    exact
      (le_sup_right :
        R₀'(H0) ≤ Submodule.span ℤ ({1} : Set (R(H0))) ⊔ R₀'(H0)) haugH0
  have hsplit : (1 : R(K)) + (χ.toCharacterRing - 1) = χ.toCharacterRing := by
    -- Split the subgroup linear character into its trivial and augmentation parts.
    abel
  have hrewrite :
      Subgroup.characterRingInduction K χ.toCharacterRing =
        Subgroup.characterRingInduction K (1 : R(K)) +
          Subgroup.characterRingInduction K (χ.toCharacterRing - 1) := by
    -- Induction is additive, so the subgroup splitting transports to the ambient character ring.
    calc
      Subgroup.characterRingInduction K χ.toCharacterRing =
          Subgroup.characterRingInduction K ((1 : R(K)) + (χ.toCharacterRing - 1)) := by
            rw [hsplit]
      _ = Subgroup.characterRingInduction K (1 : R(K)) +
            Subgroup.characterRingInduction K (χ.toCharacterRing - 1) := by
            rw [(Subgroup.characterRingInduction K).map_add]
  rw [hrewrite]
  exact Submodule.add_mem _ htriv haugH0'

/-- Helper for Remark 11-11.1-3: applying the chosen local splitting to the transported defect
equation rewrites the ambient coordinate as the selected local image plus an explicit `n`-multiple.
-/
private theorem local_coordinate_eq_top_local_image_add_zsmul_of_transported_defect
    {H0 : Type*} [Group H0] [Finite H0]
    (XH : Finset (Subgroup H0))
    (sH : ((J : XH) → R(J.1)) →ₗ[ℤ] R(H0))
    (hsH : Function.LeftInverse sH (Representation.characterRingRestriction XH).toLinearMap)
    {ξ : R(H0)} {ψ δ : (J : XH) → R(J.1)} {n : ℤ}
    (htransported :
      ((Representation.characterRingRestriction XH).toLinearMap ξ) - ψ = n • δ) :
    ξ = sH ψ + n • sH δ := by
  have hs_apply := congrArg sH htransported
  have hsplit : ξ - sH ψ = n • sH δ := by
    -- Apply the splitting to the transported family equation; the left inverse turns the global
    -- restriction term back into the original ambient coordinate.
    simpa [LinearMap.map_sub, LinearMap.map_zsmul, hsH ξ] using hs_apply
  -- Repackage the subtraction identity into the additive form used by the pairing step.
  exact eq_add_of_sub_eq hsplit

/-- Helper for Remark 11-11.1-3: if two ambient characters differ by `n` times an integral
character, then their induced linear-character pairings differ by an explicit `n`-multiple. -/
private theorem induced_linearCharacter_pairing_eq_add_n_multiple_of_characterRing_split
    {H0 : Type*} [Group H0] [Finite H0]
    (K : Subgroup H0) (χ : K →* ℂˣ) {ξ θ η : R(H0)} {n : ℤ}
    (hsplit : ξ = θ + n • η) :
    ∃ m : ℤ,
      ⟪Ind[K](χ.toRepresentation.character), (ξ : H0 → ℂ)⟫ =
        ⟪Ind[K](χ.toRepresentation.character), (θ : H0 → ℂ)⟫ +
          algebraMap ℤ ℂ (n * m) := by
  let ηcf : classFunctionSubmodule ℂ H0 :=
    ⟨(η : H0 → ℂ), by
      -- Any element of the character ring is already a bundled class function.
      rw [mem_classFunctionSubmodule_iff]
      exact isClassFunction_of_mem_characterRingOverField _ η.property⟩
  have hpair_int :
      ⟪Ind[K](χ.toRepresentation.character), (η : H0 → ℂ)⟫ ∈ Set.range (algebraMap ℤ ℂ) := by
    have hrestrict_pair :
        ⟪Ind[K](χ.toRepresentation.character), (η : H0 → ℂ)⟫ =
          ⟪(χ.toCharacterRing : K → ℂ),
              (((Subgroup.characterRingRestrictionOfLe (show K ≤ ⊤ from le_top) η : R(K)) :
                K → ℂ))⟫ := by
      -- Frobenius reciprocity rewrites the induced pairing as a pairing on the subgroup
      -- restriction of `η`.
      simpa [ηcf, Subgroup.classFunctionRestriction_apply,
        Subgroup.characterRingOverFieldRestrictionOfLe_apply] using
        (groupFunctionPairing_induced_linearCharacter_eq_restriction
          (K := K) (α := χ) (x := ηcf))
    have hpairK :
        ⟪(χ.toCharacterRing : K → ℂ),
            (((Subgroup.characterRingRestrictionOfLe (show K ≤ ⊤ from le_top) η : R(K)) :
              K → ℂ))⟫ ∈ Set.range (algebraMap ℤ ℂ) :=
      pairing_mem_range_int_of_mem_characterRing_with_linear_character_local
        (η := Subgroup.characterRingRestrictionOfLe (show K ≤ ⊤ from le_top) η) (χ := χ)
    rwa [hrestrict_pair] at hpairK
  rcases hpair_int with ⟨m, hm⟩
  refine ⟨m, ?_⟩
  -- Rewrite `ξ` as `θ + n • η`, then isolate the `n`-multiple contribution using bilinearity.
  calc
    ⟪Ind[K](χ.toRepresentation.character), (ξ : H0 → ℂ)⟫ =
        ⟪Ind[K](χ.toRepresentation.character), ((θ + n • η : R(H0)) : H0 → ℂ)⟫ := by
          rw [hsplit]
    _ = ⟪Ind[K](χ.toRepresentation.character), (θ : H0 → ℂ)⟫ +
          ⟪Ind[K](χ.toRepresentation.character), ((n • η : R(H0)) : H0 → ℂ)⟫ := by
          exact
            Representation.groupFunctionPairing_add_right
              (Ind[K](χ.toRepresentation.character))
              (θ : H0 → ℂ)
              ((n • η : R(H0)) : H0 → ℂ)
    _ = ⟪Ind[K](χ.toRepresentation.character), (θ : H0 → ℂ)⟫ +
          (n : ℂ) * ⟪Ind[K](χ.toRepresentation.character), (η : H0 → ℂ)⟫ := by
          rw [Representation.groupFunctionPairing_smul_right]
          simp [zsmul_eq_mul]
    _ = ⟪Ind[K](χ.toRepresentation.character), (θ : H0 → ℂ)⟫ +
          (n : ℂ) * algebraMap ℤ ℂ m := by
          rw [hm]
    _ = ⟪Ind[K](χ.toRepresentation.character), (θ : H0 → ℂ)⟫ +
          algebraMap ℤ ℂ (n * m) := by
          simp [Int.cast_mul]

/-- Helper for Remark 11-11.1-3: once the transported `J`-coordinate pairing of the ambient
family is divisible by `n` in `ℤ`, the corresponding proper-subgroup pairing against the top local
image is also divisible by `n`. -/
private theorem proper_induced_pairing_divisible_of_transport_pairing_int_divisible
    (X : Finset (Subgroup G))
    (hXelem : ∀ H : Subgroup G, H ∈ X ↔ IsElementary H)
    {x : (H : X) → R(H.1)} {t : elementary_coherence_target X hXelem} {n : ℤ}
    (hdx : elementary_coherence_defect X hXelem x = n • t)
    (H : X)
    (sH : ((J : (Finset.univ : Finset (Subgroup H.1))) → R(J.1)) →ₗ[ℤ] R(H.1))
    (hsH : Function.LeftInverse sH
      (Representation.characterRingRestriction (Finset.univ : Finset (Subgroup H.1))).toLinearMap)
    (J : Subgroup H.1) (α : J →* ℂˣ) :
    let KX : X := ⟨J.map H.1.subtype,
      (hXelem (J.map H.1.subtype)).2 <|
        isElementary_of_mulEquiv_local
          (J.equivMapOfInjective H.1.subtype H.1.subtype_injective)
          (subgroup_isElementary_of_isElementary_local J ((hXelem H.1).1 H.2))⟩
    let XH : Finset (Subgroup H.1) := Finset.univ
    let ψH : (K : XH) → R(K.1) := fun K ↦
      Subgroup.characterRingTransport
        (K.1.equivMapOfInjective H.1.subtype H.1.subtype_injective)
        (x ⟨K.1.map H.1.subtype,
          (hXelem (K.1.map H.1.subtype)).2 <|
            isElementary_of_mulEquiv_local
              (K.1.equivMapOfInjective H.1.subtype H.1.subtype_injective)
              (subgroup_isElementary_of_isElementary_local K.1 ((hXelem H.1).1 H.2))⟩)
    let ξH : R(H.1) := sH ψH
    (∃ c : ℤ, linear_character_pairing_int H.1 J α (x KX) = n * c) →
      ∃ b : ℤ,
        ⟪Ind[J](α.toRepresentation.character), (ξH : H.1 → ℂ)⟫ =
          algebraMap ℤ ℂ (n * b) := by
  classical
  dsimp
  intro hpair_int
  let KX : X := ⟨J.map H.1.subtype,
    (hXelem (J.map H.1.subtype)).2 <|
      isElementary_of_mulEquiv_local
        (J.equivMapOfInjective H.1.subtype H.1.subtype_injective)
        (subgroup_isElementary_of_isElementary_local J ((hXelem H.1).1 H.2))⟩
  let XH : Finset (Subgroup H.1) := Finset.univ
  let ψH : (K : XH) → R(K.1) := fun K ↦
    Subgroup.characterRingTransport
      (K.1.equivMapOfInjective H.1.subtype H.1.subtype_injective)
      (x ⟨K.1.map H.1.subtype,
        (hXelem (K.1.map H.1.subtype)).2 <|
          isElementary_of_mulEquiv_local
            (K.1.equivMapOfInjective H.1.subtype H.1.subtype_injective)
            (subgroup_isElementary_of_isElementary_local K.1 ((hXelem H.1).1 H.2))⟩)
  let δH : (K : XH) → R(K.1) := fun K ↦
    let KX' : X := ⟨K.1.map H.1.subtype,
      (hXelem (K.1.map H.1.subtype)).2 <|
        isElementary_of_mulEquiv_local
          (K.1.equivMapOfInjective H.1.subtype H.1.subtype_injective)
          (subgroup_isElementary_of_isElementary_local K.1 ((hXelem H.1).1 H.2))⟩
    let pK : elementary_restriction_relation X := ⟨(H, KX'), subgroup_chain_map_le_local H.1 K.1⟩
    Subgroup.characterRingTransport
      (K.1.equivMapOfInjective H.1.subtype H.1.subtype_injective)
      (t.1 pK)
  let ξH : R(H.1) := sH ψH
  have htransported :
      ((Representation.characterRingRestriction XH).toLinearMap (x H)) - ψH = n • δH :=
    transported_subgroup_family_defect_eq_zsmul X hXelem hdx H
  let fH : R(H.1) →ₗ[ℤ] ((K : XH) → R(K.1)) := (Representation.characterRingRestriction XH).toLinearMap
  let rH : ((K : XH) → R(K.1)) →ₗ[ℤ] ((K : XH) → R(K.1)) := LinearMap.id - fH.comp sH
  have hresidual : rH ψH = (-n) • rH δH :=
    local_residual_projector_eq_neg_zsmul XH sH hsH htransported
  let J0 : XH := ⟨J, by simp [XH]⟩
  have himage_residual : fH (sH ψH) - ψH = n • rH δH := by
    have hresidual' : ψH - fH (sH ψH) = (-n) • rH δH := by
      -- Apply the residual projector first, then rewrite the resulting identity in image-minus-error
      -- form so the local pairing decomposition lemma can consume it directly.
      simpa [rH, fH, Pi.sub_apply, LinearMap.sub_apply, LinearMap.comp_apply] using hresidual
    have hneg := congrArg Neg.neg hresidual'
    simpa [Pi.neg_apply, Pi.smul_apply, zsmul_eq_mul, sub_eq_add_neg, add_comm, add_left_comm,
      add_assoc, mul_comm, mul_left_comm, mul_assoc] using hneg
  obtain ⟨m, hdecomp⟩ :=
    local_residual_pairing_decomposition_of_defect_multiple XH sH hsH himage_residual J0 α
  rcases hpair_int with ⟨c, hc⟩
  have hpair_transport :
      ⟪(α.toCharacterRing : J → ℂ), (ψH J0 : J → ℂ)⟫ = algebraMap ℤ ℂ (n * c) := by
    -- The transported `J`-coordinate is exactly the ambient `KX`-coordinate of `x`.
    calc
      ⟪(α.toCharacterRing : J → ℂ), (ψH J0 : J → ℂ)⟫ =
          algebraMap ℤ ℂ (linear_character_pairing_int H.1 J α (x KX)) := by
            exact subgroup_linear_character_pairing_int_transport_eq H.1 J α (x KX)
      _ = algebraMap ℤ ℂ (n * c) := by rw [hc]
  have hcoord_pairing :
      ⟪(α.toCharacterRing : J → ℂ),
          (((Representation.characterRingRestriction XH) ξH J0 : R(J)) : J → ℂ)⟫ =
        algebraMap ℤ ℂ (n * (c - m)) := by
    have hsum :
        ⟪(α.toCharacterRing : J → ℂ),
            (((Representation.characterRingRestriction XH) ξH J0 : R(J)) : J → ℂ)⟫ +
          algebraMap ℤ ℂ (n * m) =
        algebraMap ℤ ℂ (n * c) := by
      calc
        ⟪(α.toCharacterRing : J → ℂ),
            (((Representation.characterRingRestriction XH) ξH J0 : R(J)) : J → ℂ)⟫ +
              algebraMap ℤ ℂ (n * m) =
            ⟪(α.toCharacterRing : J → ℂ), (ψH J0 : J → ℂ)⟫ := by
              symm
              exact hdecomp
        _ = algebraMap ℤ ℂ (n * c) := hpair_transport
    have hsub :
        ⟪(α.toCharacterRing : J → ℂ),
            (((Representation.characterRingRestriction XH) ξH J0 : R(J)) : J → ℂ)⟫ =
          algebraMap ℤ ℂ (n * c) - algebraMap ℤ ℂ (n * m) :=
      eq_sub_iff_add_eq.mpr hsum
    -- Simplify the difference of the two `n`-multiples into a single witness.
    simpa [Int.cast_mul, sub_eq_add_neg, mul_add, mul_assoc, add_comm, add_left_comm, add_assoc]
      using hsub
  refine ⟨c - m, ?_⟩
  -- Rewrite the explicit local coordinate back to the ambient induced pairing on `H`.
  calc
    ⟪Ind[J](α.toRepresentation.character), (ξH : H.1 → ℂ)⟫ =
        ⟪(α.toCharacterRing : J → ℂ),
            (((Representation.characterRingRestriction XH) ξH J0 : R(J)) : J → ℂ)⟫ := by
              symm
              simpa [ξH] using
                (top_local_coordinate_pairing_eq_induced_pairing
                  (sH := sH) (ψH := ψH) (K := J) (χ := α))
    _ = algebraMap ℤ ℂ (n * (c - m)) := hcoord_pairing

/-- Helper for Remark 11-11.1-3: pairing the coatom quotient-character identity against a fixed
local character rewrites the induced trivial pairing as the sum of the trivial-line contribution
and the quotient linear-character differences. -/
private theorem induced_trivial_pairing_eq_index_trivial_pairing_add_quotient_difference_sum
    {H0 : Type*} [Group H0] [Finite H0]
    (M : Subgroup H0) [M.Normal]
    (hcomm : ∀ a b : H0 ⧸ M, a * b = b * a)
    [Fintype ((H0 ⧸ M) →* ℂˣ)]
    (ξ : R(H0)) :
    ⟪(Subgroup.characterRingInduction M (1 : R(M)) : H0 → ℂ), (ξ : H0 → ℂ)⟫ =
      (M.index : ℂ) * ⟪((1 : R(H0)) : H0 → ℂ), (ξ : H0 → ℂ)⟫ +
        ∑ β : (H0 ⧸ M) →* ℂˣ,
          ⟪((((β.comp (QuotientGroup.mk' M)).toCharacterRing - 1 : R(H0)) : H0 → ℂ),
              (ξ : H0 → ℂ)⟫ := by
  let pairLeft : R(H0) →ₗ[ℤ] ℂ :=
    { toFun := fun η ↦ ⟪(η : H0 → ℂ), (ξ : H0 → ℂ)⟫
      map_add' := by
        intro η θ
        exact Representation.groupFunctionPairing_add_left (η : H0 → ℂ) (θ : H0 → ℂ) (ξ : H0 → ℂ)
      map_smul' := by
        intro a η
        simpa [zsmul_eq_mul] using
          (Representation.groupFunctionPairing_smul_left
            (a := (a : ℂ)) (φ := (η : H0 → ℂ)) (ψ := (ξ : H0 → ℂ))) }
  have hpair_sub :
      ⟪(((Subgroup.characterRingInduction M (1 : R(M)) - (M.index : ℤ) • (1 : R(H0))) : R(H0)) :
          H0 → ℂ), (ξ : H0 → ℂ)⟫ =
        ∑ β : (H0 ⧸ M) →* ℂˣ,
          ⟪((((β.comp (QuotientGroup.mk' M)).toCharacterRing - 1 : R(H0)) : H0 → ℂ),
              (ξ : H0 → ℂ)⟫ := by
    -- Apply the left-linear pairing functional to the quotient-character difference identity.
    simpa [pairLeft, map_sub, zsmul_eq_mul] using
      congrArg pairLeft
        (Subgroup.induced_trivial_sub_index_smul_one_eq_sum_quotient_linearCharacter_differences
          (H := M) hcomm)
  have hpair_eq :
      ⟪(Subgroup.characterRingInduction M (1 : R(M)) : H0 → ℂ), (ξ : H0 → ℂ)⟫ -
          (M.index : ℂ) * ⟪((1 : R(H0)) : H0 → ℂ), (ξ : H0 → ℂ)⟫ =
        ∑ β : (H0 ⧸ M) →* ℂˣ,
          ⟪((((β.comp (QuotientGroup.mk' M)).toCharacterRing - 1 : R(H0)) : H0 → ℂ),
              (ξ : H0 → ℂ)⟫ := by
    simpa [Representation.groupFunctionPairing_smul_left, zsmul_eq_mul] using hpair_sub
  -- Move the trivial-line term to the right to recover the source-faithful additive decomposition.
  exact eq_add_of_sub_eq hpair_eq

/-- Helper for Remark 11-11.1-3: inducing a linear-character difference from the top subgroup
identifies it with the corresponding ambient linear-character difference. -/
private theorem top_induced_difference_eq_ambient_difference
    {H0 : Type*} [Group H0] [Finite H0]
    (α : (⊤ : Subgroup H0) →* ℂˣ) :
    let β : H0 →* ℂˣ := α.comp Subgroup.topEquiv.symm.toMonoidHom
    Subgroup.characterRingInduction (⊤ : Subgroup H0) (α.toCharacterRing - 1) =
      (β.toCharacterRing - 1 : R(H0)) := by
  dsimp
  let β : H0 →* ℂˣ := α.comp Subgroup.topEquiv.symm.toMonoidHom
  have hα :
      ((β.comp Subgroup.topEquiv.toMonoidHom).toCharacterRing : R((⊤ : Subgroup H0))) =
        α.toCharacterRing := by
    -- Transport the top-subgroup linear character across `⊤ ≃ H0` before inducing.
    apply Subtype.ext
    ext x
    simp [β]
  have htop_one :
      Subgroup.characterRingInduction (⊤ : Subgroup H0) (1 : R((⊤ : Subgroup H0))) =
        (1 : R(H0)) := by
    -- Induction from the full subgroup fixes the trivial character.
    simpa using
      characterRingInduction_top_toCharacterRing (G := H0) (β := (1 : H0 →* ℂˣ))
  -- Rewrite the top-subgroup input in the canonical `β.comp topEquiv` form and then induce.
  calc
    Subgroup.characterRingInduction (⊤ : Subgroup H0) (α.toCharacterRing - 1) =
        Subgroup.characterRingInduction (⊤ : Subgroup H0)
          (((β.comp Subgroup.topEquiv.toMonoidHom).toCharacterRing : R((⊤ : Subgroup H0))) - 1) := by
            rw [hα]
    _ =
        Subgroup.characterRingInduction (⊤ : Subgroup H0)
            ((β.comp Subgroup.topEquiv.toMonoidHom).toCharacterRing : R((⊤ : Subgroup H0))) -
          Subgroup.characterRingInduction (⊤ : Subgroup H0) (1 : R((⊤ : Subgroup H0))) := by
            rw [(Subgroup.characterRingInduction (⊤ : Subgroup H0)).map_sub]
    _ = (β.toCharacterRing : R(H0)) -
          Subgroup.characterRingInduction (⊤ : Subgroup H0) (1 : R((⊤ : Subgroup H0))) := by
            rw [characterRingInduction_top_toCharacterRing (G := H0) (β := β)]
    _ = (β.toCharacterRing - 1 : R(H0)) := by
            rw [htop_one]

/-- Helper for Remark 11-11.1-3: rewriting the induced top-subgroup difference to the ambient
linear-character difference does not change its pairing with a fixed test character. -/
private theorem ambient_difference_pairing_eq_top_induced_difference_pairing
    {H0 : Type*} [Group H0] [Finite H0]
    (ξ : R(H0)) (α : (⊤ : Subgroup H0) →* ℂˣ) :
    ⟪((((α.comp Subgroup.topEquiv.symm.toMonoidHom).toCharacterRing - 1 : R(H0)) :
          H0 → ℂ),
        (ξ : H0 → ℂ)⟫ =
      ⟪((Subgroup.characterRingInduction (⊤ : Subgroup H0)
            (α.toCharacterRing - 1) : R(H0)) : H0 → ℂ),
          (ξ : H0 → ℂ)⟫ := by
  -- Rewrite the top-induced difference to the canonical ambient difference term.
  rw [top_induced_difference_eq_ambient_difference (H0 := H0) α]

/-- Helper for Remark 11-11.1-3: inducing a linear-character difference from the top subgroup
recovers the corresponding ambient linear-character difference, so the `E = ⊤` generators already
lie in LinearRepresentations_Serre_1977's augmentation subgroup. -/
private theorem top_induced_linearCharacter_difference_mem_augmentation_of_isElementary
    {H0 : Type*} [Group H0] [Finite H0]
    (hH0 : IsElementary H0) (α : (⊤ : Subgroup H0) →* ℂˣ) :
    Subgroup.characterRingInduction (⊤ : Subgroup H0) (α.toCharacterRing - 1) ∈ R₀'(H0) := by
  let β : H0 →* ℂˣ := α.comp Subgroup.topEquiv.symm.toMonoidHom
  -- Reduce the top-subgroup induction generator to the ambient linear-character difference owner.
  rw [top_induced_difference_eq_ambient_difference α]
  exact
    linearCharacter_difference_mem_elementaryLinearCharacterAugmentationSpan_of_isElementary
      (G := H0) hH0 β

/-- Helper for Remark 11-11.1-3: if the ambient group is trivial, every linear character of the
top subgroup is the trivial character. -/
private theorem top_linearCharacter_eq_one_of_bot_eq_top_local
    {H0 : Type*} [Group H0]
    (htrivial : (⊥ : Subgroup H0) = ⊤)
    (α : (⊤ : Subgroup H0) →* ℂˣ) :
    α = 1 := by
  have hone : ∀ x : H0, x = 1 := by
    intro x
    have hx : x ∈ (⊥ : Subgroup H0) := by
      rw [htrivial]
      simp
    simpa using hx
  ext x
  have hx : x = 1 := by
    apply Subtype.ext
    exact hone x.1
  -- The top subgroup has only one element, so every multiplicative character is trivial.
  simp [hx]

/-- Helper for Remark 11-11.1-3: if the ambient group is trivial, the induced top-subgroup
linear-character difference vanishes. -/
private theorem top_induced_difference_eq_zero_of_bot_eq_top_local
    {H0 : Type*} [Group H0]
    (htrivial : (⊥ : Subgroup H0) = ⊤)
    (α : (⊤ : Subgroup H0) →* ℂˣ) :
    Subgroup.characterRingInduction (⊤ : Subgroup H0) (α.toCharacterRing - 1) = 0 := by
  -- After collapsing the unique top character to `1`, the induced difference is literally zero.
  rw [top_linearCharacter_eq_one_of_bot_eq_top_local htrivial α]
  simp [Subgroup.toCharacterRing_one]

/-- Helper for Remark 11-11.1-3: transporting a nontrivial top-subgroup character to the ambient
group still has proper kernel. -/
private theorem kernel_of_nontrivial_top_character_lt_top_local
    {H0 : Type*} [Group H0]
    (α : (⊤ : Subgroup H0) →* ℂˣ) (hα : α ≠ 1) :
    let β : H0 →* ℂˣ := α.comp Subgroup.topEquiv.symm.toMonoidHom
    β.ker < ⊤ := by
  dsimp
  refine lt_top_iff_ne_top.mpr ?_
  intro hker
  apply hα
  ext x
  have hxker : x.1 ∈ (α.comp Subgroup.topEquiv.symm.toMonoidHom).ker := by
    -- The assumed kernel equality forces every element into the transported kernel.
    rw [hker]
    simp
  -- Reading kernel membership back through `⊤ ≃ H0` shows the original top character is trivial.
  simpa [MonoidHom.mem_ker] using hxker

/-- Helper for Remark 11-11.1-3: when `H` is trivial, the transported family indexed by all
subgroups of `H` is just the ordinary restriction family of the ambient coordinate `x H`. -/
private theorem singleton_transported_family_eq_ambient_restriction
    (X : Finset (Subgroup G))
    (hXelem : ∀ H : Subgroup G, H ∈ X ↔ IsElementary H)
    {x : (H : X) → R(H.1)}
    (H : X)
    (htrivial : (⊥ : Subgroup H.1) = ⊤) :
    let XH : Finset (Subgroup H.1) := Finset.univ
    let ψH : (J : XH) → R(J.1) := fun J ↦
      Subgroup.characterRingTransport
        (J.1.equivMapOfInjective H.1.subtype H.1.subtype_injective)
        (x ⟨J.1.map H.1.subtype,
          (hXelem (J.1.map H.1.subtype)).2 <|
            isElementary_of_mulEquiv_local
              (J.1.equivMapOfInjective H.1.subtype H.1.subtype_injective)
              (subgroup_isElementary_of_isElementary_local J.1 ((hXelem H.1).1 H.2))⟩)
    ψH = (Representation.characterRingRestriction XH).toLinearMap (x H) := by
  classical
  dsimp
  ext J j
  have hJtop : J.1 = ⊤ := by
    apply le_antisymm le_top
    rw [← htrivial]
    exact bot_le
  have hJ :
      J = ⟨(⊤ : Subgroup H.1), by simp⟩ := by
    apply Subtype.ext
    exact hJtop
  subst hJ
  have htopX :
      (⟨(⊤ : Subgroup H.1).map H.1.subtype,
          (hXelem ((⊤ : Subgroup H.1).map H.1.subtype)).2 <|
            isElementary_of_mulEquiv_local
              ((⊤ : Subgroup H.1).equivMapOfInjective H.1.subtype H.1.subtype_injective)
              (subgroup_isElementary_of_isElementary_local (⊤ : Subgroup H.1)
                ((hXelem H.1).1 H.2))⟩ : X) = H := by
    apply Subtype.ext
    simp
  -- With only the top subgroup left, the transported coordinate is literally the ambient one.
  simp [Representation.characterRingRestriction_apply, Subgroup.characterRingTransport_apply,
    Subgroup.characterRingOverFieldRestrictionOfLe_apply, Subgroup.coe_equivMapOfInjective_apply,
    htopX]

/-- Helper for Remark 11-11.1-3: in the trivial-ambient branch, gluing the singleton family back
with `sH` recovers the original ambient coordinate `x H`. -/
private theorem singleton_top_local_image_eq_ambient_coordinate
    (X : Finset (Subgroup G))
    (hXelem : ∀ H : Subgroup G, H ∈ X ↔ IsElementary H)
    {x : (H : X) → R(H.1)}
    (H : X)
    (sH : ((J : (Finset.univ : Finset (Subgroup H.1))) → R(J.1)) →ₗ[ℤ] R(H.1))
    (hsH : Function.LeftInverse sH
      (Representation.characterRingRestriction (Finset.univ : Finset (Subgroup H.1))).toLinearMap)
    (htrivial : (⊥ : Subgroup H.1) = ⊤) :
    let XH : Finset (Subgroup H.1) := Finset.univ
    let ψH : (J : XH) → R(J.1) := fun J ↦
      Subgroup.characterRingTransport
        (J.1.equivMapOfInjective H.1.subtype H.1.subtype_injective)
        (x ⟨J.1.map H.1.subtype,
          (hXelem (J.1.map H.1.subtype)).2 <|
            isElementary_of_mulEquiv_local
              (J.1.equivMapOfInjective H.1.subtype H.1.subtype_injective)
              (subgroup_isElementary_of_isElementary_local J.1 ((hXelem H.1).1 H.2))⟩)
    sH ψH = x H := by
  classical
  dsimp
  -- First collapse the singleton family to the genuine restriction family of `x H`.
  rw [singleton_transported_family_eq_ambient_restriction X hXelem H htrivial]
  exact hsH (x H)

/-- Helper for Remark 11-11.1-3: if the ambient subgroup `H` is trivial, then the transported
singleton defect vanishes once the scalar `n` is nonzero. -/
private theorem singleton_transported_defect_eq_zero_of_bot_eq_top_local
    (X : Finset (Subgroup G))
    (hXelem : ∀ H : Subgroup G, H ∈ X ↔ IsElementary H)
    {x : (H : X) → R(H.1)} {t : elementary_coherence_target X hXelem} {n : ℤ}
    (hn : n ≠ 0)
    (hdx : elementary_coherence_defect X hXelem x = n • t)
    (H : X)
    (htrivial : (⊥ : Subgroup H.1) = ⊤) :
    let XH : Finset (Subgroup H.1) := Finset.univ
    let δH : (J : XH) → R(J.1) := fun J ↦
      let JX : X := ⟨J.1.map H.1.subtype,
        (hXelem (J.1.map H.1.subtype)).2 <|
          isElementary_of_mulEquiv_local
            (J.1.equivMapOfInjective H.1.subtype H.1.subtype_injective)
            (subgroup_isElementary_of_isElementary_local J.1 ((hXelem H.1).1 H.2))⟩
      let pJ : elementary_restriction_relation X := ⟨(H, JX), subgroup_chain_map_le_local H.1 J.1⟩
      Subgroup.characterRingTransport
        (J.1.equivMapOfInjective H.1.subtype H.1.subtype_injective)
        (t.1 pJ)
    δH = 0 := by
  classical
  dsimp
  let XH : Finset (Subgroup H.1) := Finset.univ
  let ψH : (J : XH) → R(J.1) := fun J ↦
    Subgroup.characterRingTransport
      (J.1.equivMapOfInjective H.1.subtype H.1.subtype_injective)
      (x ⟨J.1.map H.1.subtype,
        (hXelem (J.1.map H.1.subtype)).2 <|
          isElementary_of_mulEquiv_local
            (J.1.equivMapOfInjective H.1.subtype H.1.subtype_injective)
            (subgroup_isElementary_of_isElementary_local J.1 ((hXelem H.1).1 H.2))⟩)
  let δH : (J : XH) → R(J.1) := fun J ↦
    let JX : X := ⟨J.1.map H.1.subtype,
      (hXelem (J.1.map H.1.subtype)).2 <|
        isElementary_of_mulEquiv_local
          (J.1.equivMapOfInjective H.1.subtype H.1.subtype_injective)
          (subgroup_isElementary_of_isElementary_local J.1 ((hXelem H.1).1 H.2))⟩
    let pJ : elementary_restriction_relation X := ⟨(H, JX), subgroup_chain_map_le_local H.1 J.1⟩
    Subgroup.characterRingTransport
      (J.1.equivMapOfInjective H.1.subtype H.1.subtype_injective)
      (t.1 pJ)
  have htransported :
      ((Representation.characterRingRestriction XH).toLinearMap (x H)) - ψH = n • δH :=
    transported_subgroup_family_defect_eq_zsmul X hXelem hdx H
  have hsingleton :
      ψH = (Representation.characterRingRestriction XH).toLinearMap (x H) :=
    singleton_transported_family_eq_ambient_restriction X hXelem H htrivial
  have hzsmul_zero : n • δH = 0 := by
    -- The transported family is already the actual restriction family, so its defect side is zero.
    calc
      n • δH = ((Representation.characterRingRestriction XH).toLinearMap (x H)) - ψH := by
        simpa using htransported.symm
      _ = 0 := by simpa [hsingleton]
  -- Cancel the nonzero scalar coordinatewise in the singleton family.
  ext J
  apply characterRing_zsmul_left_cancel (H := J.1) hn
  simpa [Pi.smul_apply] using congrArg (fun η : (K : XH) → R(K.1) ↦ η J) hzsmul_zero

/-- Helper for Remark 11-11.1-3: the coatom package already gives the top-local pairing witness
needed by the residual argument, because a top character is the sum of the trivial line and its
top-induced difference. -/
private theorem top_local_pairing_divisible_of_trivial_and_top_difference_pairings
    {H0 : Type*} [Group H0] [Finite H0] {n : ℤ}
    (sH : ((J : (Finset.univ : Finset (Subgroup H0))) → R(J.1)) →ₗ[ℤ] R(H0))
    (ψH : (J : (Finset.univ : Finset (Subgroup H0))) → R(J.1))
    (α : (⊤ : Subgroup H0) →* ℂˣ)
    (htriv :
      ∃ b₀ : ℤ,
        ⟪((1 : R(H0)) : H0 → ℂ), (((sH ψH : R(H0)) : H0 → ℂ))⟫ =
          algebraMap ℤ ℂ (n * b₀))
    (hdiff :
      ∃ b : ℤ,
        ⟪((Subgroup.characterRingInduction (⊤ : Subgroup H0)
              (α.toCharacterRing - 1) : R(H0)) : H0 → ℂ),
            (((sH ψH : R(H0)) : H0 → ℂ))⟫ =
          algebraMap ℤ ℂ (n * b)) :
    let XH : Finset (Subgroup H0) := Finset.univ
    let K0 : XH := ⟨⊤, by simp [XH]⟩
    ∃ b : ℤ,
      ⟪(α.toCharacterRing : (⊤ : Subgroup H0) → ℂ),
          (((Representation.characterRingRestriction XH) (sH ψH) K0 : R((⊤ : Subgroup H0))) :
            (⊤ : Subgroup H0) → ℂ)⟫ =
        algebraMap ℤ ℂ (n * b) := by
  classical
  dsimp
  let ξH : R(H0) := sH ψH
  have hcoord :
      ⟪(α.toCharacterRing : (⊤ : Subgroup H0) → ℂ),
          (((Representation.characterRingRestriction (Finset.univ : Finset (Subgroup H0))) ξH
              ⟨⊤, by simp⟩ : R((⊤ : Subgroup H0))) : (⊤ : Subgroup H0) → ℂ)⟫ =
        ⟪((Subgroup.characterRingInduction (⊤ : Subgroup H0) α.toCharacterRing : R(H0)) :
              H0 → ℂ),
            (ξH : H0 → ℂ)⟫ := by
    -- Rewrite the explicit top coordinate as the ambient induced top character.
    simpa [ξH, Subgroup.characterRingInduction_apply] using
      (top_local_coordinate_pairing_eq_induced_pairing
        (sH := sH) (ψH := ψH) (K := (⊤ : Subgroup H0)) (χ := α))
  have htop_one :
      Subgroup.characterRingInduction (⊤ : Subgroup H0) (1 : R((⊤ : Subgroup H0))) =
        (1 : R(H0)) := by
    -- Induction from the full subgroup fixes the trivial character.
    calc
      Subgroup.characterRingInduction (⊤ : Subgroup H0) (1 : R((⊤ : Subgroup H0))) =
          Subgroup.characterRingInduction (⊤ : Subgroup H0)
            (((1 : (⊤ : Subgroup H0) →* ℂˣ).toCharacterRing) : R((⊤ : Subgroup H0))) := by
              rw [Subgroup.toCharacterRing_one]
      _ = ((1 : H0 →* ℂˣ).toCharacterRing : R(H0)) := by
            simpa using
              characterRingInduction_top_toCharacterRing (G := H0) (β := (1 : H0 →* ℂˣ))
      _ = (1 : R(H0)) := by
            ext g
            simp
  have hind_split :
      Subgroup.characterRingInduction (⊤ : Subgroup H0) α.toCharacterRing =
        (1 : R(H0)) +
          Subgroup.characterRingInduction (⊤ : Subgroup H0) (α.toCharacterRing - 1) := by
    have hsplit_top : ((1 : R((⊤ : Subgroup H0))) + (α.toCharacterRing - 1)) = α.toCharacterRing := by
      abel
    -- Split the top character into its trivial and augmentation parts before inducing.
    calc
      Subgroup.characterRingInduction (⊤ : Subgroup H0) α.toCharacterRing =
          Subgroup.characterRingInduction (⊤ : Subgroup H0)
            ((1 : R((⊤ : Subgroup H0))) + (α.toCharacterRing - 1)) := by
              rw [← hsplit_top]
      _ =
          Subgroup.characterRingInduction (⊤ : Subgroup H0) (1 : R((⊤ : Subgroup H0))) +
            Subgroup.characterRingInduction (⊤ : Subgroup H0) (α.toCharacterRing - 1) := by
              rw [(Subgroup.characterRingInduction (⊤ : Subgroup H0)).map_add]
      _ = (1 : R(H0)) +
            Subgroup.characterRingInduction (⊤ : Subgroup H0) (α.toCharacterRing - 1) := by
              rw [htop_one]
  rcases htriv with ⟨b₀, hb₀⟩
  rcases hdiff with ⟨b, hb⟩
  refine ⟨b₀ + b, ?_⟩
  -- Add the trivial-line witness to the top-difference witness, then convert back to the top
  -- local coordinate.
  calc
    ⟪(α.toCharacterRing : (⊤ : Subgroup H0) → ℂ),
        (((Representation.characterRingRestriction (Finset.univ : Finset (Subgroup H0))) ξH
            ⟨⊤, by simp⟩ : R((⊤ : Subgroup H0))) : (⊤ : Subgroup H0) → ℂ)⟫ =
      ⟪((Subgroup.characterRingInduction (⊤ : Subgroup H0) α.toCharacterRing : R(H0)) :
            H0 → ℂ),
          (ξH : H0 → ℂ)⟫ := hcoord
    _ =
      ⟪(((1 : R(H0)) +
            Subgroup.characterRingInduction (⊤ : Subgroup H0) (α.toCharacterRing - 1) :
              R(H0)) : H0 → ℂ),
          (ξH : H0 → ℂ)⟫ := by
            rw [hind_split]
    _ =
      ⟪((1 : R(H0)) : H0 → ℂ), (ξH : H0 → ℂ)⟫ +
        ⟪((Subgroup.characterRingInduction (⊤ : Subgroup H0) (α.toCharacterRing - 1) :
              R(H0)) : H0 → ℂ),
            (ξH : H0 → ℂ)⟫ := by
              exact
                Representation.groupFunctionPairing_add_left
                  (1 : H0 → ℂ)
                  ((Subgroup.characterRingInduction (⊤ : Subgroup H0) (α.toCharacterRing - 1) :
                    R(H0)) : H0 → ℂ)
                  (ξH : H0 → ℂ)
    _ = algebraMap ℤ ℂ (n * b₀) + algebraMap ℤ ℂ (n * b) := by rw [hb₀, hb]
    _ = algebraMap ℤ ℂ (n * (b₀ + b)) := by
          rw [← Int.cast_add]
          congr 1
          ring

/-- Helper for Remark 11-11.1-3: the remaining arithmetic step is to show that the residual
`K`-coordinate pairing extracted from the defect identity is divisible by `n` in `ℤ`. -/
private theorem residual_subgroup_pairing_int_divisible_of_given_top_local_pairing
    (X : Finset (Subgroup G))
    (hXelem : ∀ H : Subgroup G, H ∈ X ↔ IsElementary H)
    (s : ((H : X) → R(H.1)) →ₗ[ℤ] R(G))
    (hs : Function.LeftInverse s (Representation.characterRingRestriction X).toLinearMap)
    {x : (H : X) → R(H.1)} {t : elementary_coherence_target X hXelem} {n : ℤ}
    (hn : n ≠ 0) (hx : s x = 0)
    (hdx : elementary_coherence_defect X hXelem x = n • t)
    (H : X)
    (sH : ((J : (Finset.univ : Finset (Subgroup H.1))) → R(J.1)) →ₗ[ℤ] R(H.1))
    (hsH : Function.LeftInverse sH
      (Representation.characterRingRestriction (Finset.univ : Finset (Subgroup H.1))).toLinearMap)
    (K : Subgroup H.1) (χ : K →* ℂˣ)
    (htop :
      let XH : Finset (Subgroup H.1) := Finset.univ
      let ψH : (J : XH) → R(J.1) := fun J ↦
        Subgroup.characterRingTransport
          (J.1.equivMapOfInjective H.1.subtype H.1.subtype_injective)
          (x ⟨J.1.map H.1.subtype,
            (hXelem (J.1.map H.1.subtype)).2 <|
              isElementary_of_mulEquiv_local
                (J.1.equivMapOfInjective H.1.subtype H.1.subtype_injective)
                (subgroup_isElementary_of_isElementary_local J.1 ((hXelem H.1).1 H.2))⟩)
      let K0 : XH := ⟨K, by simp [XH]⟩
      ∃ b : ℤ,
        ⟪(χ.toCharacterRing : K → ℂ),
            (((Representation.characterRingRestriction XH) (sH ψH) K0 : R(K)) : K → ℂ)⟫ =
          algebraMap ℤ ℂ (n * b)) :
    let KX : X := ⟨K.map H.1.subtype,
      (hXelem (K.map H.1.subtype)).2 <|
        isElementary_of_mulEquiv_local
          (K.equivMapOfInjective H.1.subtype H.1.subtype_injective)
          (subgroup_isElementary_of_isElementary_local K ((hXelem H.1).1 H.2))⟩
    ∃ m : ℤ, linear_character_pairing_int H.1 K χ (x KX) = n * m := by
  classical
  dsimp at htop ⊢
  let KX : X := ⟨K.map H.1.subtype,
    (hXelem (K.map H.1.subtype)).2 <|
      isElementary_of_mulEquiv_local
        (K.equivMapOfInjective H.1.subtype H.1.subtype_injective)
        (subgroup_isElementary_of_isElementary_local K ((hXelem H.1).1 H.2))⟩
  let XH : Finset (Subgroup H.1) := Finset.univ
  let ψH : (J : XH) → R(J.1) := fun J ↦
    Subgroup.characterRingTransport
      (J.1.equivMapOfInjective H.1.subtype H.1.subtype_injective)
      (x ⟨J.1.map H.1.subtype,
        (hXelem (J.1.map H.1.subtype)).2 <|
          isElementary_of_mulEquiv_local
            (J.1.equivMapOfInjective H.1.subtype H.1.subtype_injective)
            (subgroup_isElementary_of_isElementary_local J.1 ((hXelem H.1).1 H.2))⟩)
  let δH : (J : XH) → R(J.1) := fun J ↦
    let JX : X := ⟨J.1.map H.1.subtype,
      (hXelem (J.1.map H.1.subtype)).2 <|
        isElementary_of_mulEquiv_local
          (J.1.equivMapOfInjective H.1.subtype H.1.subtype_injective)
          (subgroup_isElementary_of_isElementary_local J.1 ((hXelem H.1).1 H.2))⟩
    let pJ : elementary_restriction_relation X := ⟨(H, JX), subgroup_chain_map_le_local H.1 J.1⟩
    Subgroup.characterRingTransport
      (J.1.equivMapOfInjective H.1.subtype H.1.subtype_injective)
      (t.1 pJ)
  have htransported :
      ((Representation.characterRingRestriction XH).toLinearMap (x H)) - ψH = n • δH :=
    transported_subgroup_family_defect_eq_zsmul X hXelem hdx H
  let fH : R(H.1) →ₗ[ℤ] ((J : XH) → R(J.1)) :=
    (Representation.characterRingRestriction XH).toLinearMap
  let rH : ((J : XH) → R(J.1)) →ₗ[ℤ] ((J : XH) → R(J.1)) := LinearMap.id - fH.comp sH
  have hresidual : rH ψH = (-n) • rH δH :=
    local_residual_projector_eq_neg_zsmul XH sH hsH htransported
  let K0 : XH := ⟨K, by simp [XH]⟩
  have himage_residual : fH (sH ψH) - ψH = n • rH δH := by
    have hresidual' : ψH - fH (sH ψH) = (-n) • rH δH := by
      -- Apply the residual projector first, then rewrite the result into image-minus-error form.
      simpa [rH, fH, Pi.sub_apply, LinearMap.sub_apply, LinearMap.comp_apply]
        using hresidual
    have hneg := congrArg Neg.neg hresidual'
    simpa [Pi.neg_apply, Pi.smul_apply, zsmul_eq_mul, sub_eq_add_neg, add_comm, add_left_comm,
      add_assoc, mul_comm, mul_left_comm, mul_assoc] using hneg
  obtain ⟨m, hdecomp⟩ :=
    local_residual_pairing_decomposition_of_defect_multiple XH sH hsH himage_residual K0 χ
  have hpair_x :
      algebraMap ℤ ℂ (linear_character_pairing_int H.1 K χ (x KX)) =
        ⟪(χ.toCharacterRing : K → ℂ), (ψH K0 : K → ℂ)⟫ := by
    -- The transported `K`-coordinate of `ψH` is exactly the ambient `KX`-coordinate of `x`.
    simpa [KX, K0, ψH] using
      (subgroup_linear_character_pairing_int_transport_eq H.1 K χ (x KX)).symm
  have hpair_decomp :
      algebraMap ℤ ℂ (linear_character_pairing_int H.1 K χ (x KX)) =
        ⟪(χ.toCharacterRing : K → ℂ),
            (((Representation.characterRingRestriction XH) (sH ψH) K0 : R(K)) : K → ℂ)⟫ +
          algebraMap ℤ ℂ (n * m) := by
    simpa [hpair_x] using hdecomp
  rcases htop with ⟨b, hb⟩
  refine ⟨b + m, ?_⟩
  apply Int.cast_injective
  -- Combine the explicit local-image divisibility witness with the residual decomposition.
  calc
    algebraMap ℤ ℂ (linear_character_pairing_int H.1 K χ (x KX)) =
        ⟪(χ.toCharacterRing : K → ℂ),
            (((Representation.characterRingRestriction XH) (sH ψH) K0 : R(K)) : K → ℂ)⟫ +
          algebraMap ℤ ℂ (n * m) := hpair_decomp
    _ = algebraMap ℤ ℂ (n * b) + algebraMap ℤ ℂ (n * m) := by rw [hb]
    _ = algebraMap ℤ ℂ ((n * b) + (n * m)) := by simp [Int.cast_add]
    _ = algebraMap ℤ ℂ (n * (b + m)) := by ring

/-- Helper for Remark 11-11.1-3: in the trivial ambient branch, the singleton local family should
already force the trivial-line pairing against the top local image to be an `n`-multiple. -/
private theorem top_local_trivial_pairing_divisible_of_residual_family
    (X : Finset (Subgroup G))
    (hXelem : ∀ H : Subgroup G, H ∈ X ↔ IsElementary H)
    (s : ((H : X) → R(H.1)) →ₗ[ℤ] R(G))
    (hs : Function.LeftInverse s (Representation.characterRingRestriction X).toLinearMap)
    {x : (H : X) → R(H.1)} {t : elementary_coherence_target X hXelem} {n : ℤ}
    (hn : n ≠ 0)
    (hx : s x = 0)
    (hdx : elementary_coherence_defect X hXelem x = n • t)
    (H : X)
    (sH : ((J : (Finset.univ : Finset (Subgroup H.1))) → R(J.1)) →ₗ[ℤ] R(H.1))
    (hsH : Function.LeftInverse sH
      (Representation.characterRingRestriction (Finset.univ : Finset (Subgroup H.1))).toLinearMap) :
    let XH : Finset (Subgroup H.1) := Finset.univ
    let ψH : (J : XH) → R(J.1) := fun J ↦
      Subgroup.characterRingTransport
        (J.1.equivMapOfInjective H.1.subtype H.1.subtype_injective)
        (x ⟨J.1.map H.1.subtype,
          (hXelem (J.1.map H.1.subtype)).2 <|
            isElementary_of_mulEquiv_local
              (J.1.equivMapOfInjective H.1.subtype H.1.subtype_injective)
              (subgroup_isElementary_of_isElementary_local J.1 ((hXelem H.1).1 H.2))⟩)
    let ξH : R(H.1) := sH ψH
    ∃ b₀ : ℤ,
      ⟪((1 : R(H.1)) : H.1 → ℂ), (ξH : H.1 → ℂ)⟫ =
        algebraMap ℤ ℂ (n * b₀) := by
  classical
  dsimp
  obtain ⟨y, hy⟩ :=
    residual_family_divisible_of_multiple_coherence_defect X hXelem s hs hn hx hdx
  let XH : Finset (Subgroup H.1) := Finset.univ
  let ψH : (J : XH) → R(J.1) := fun J ↦
    Subgroup.characterRingTransport
      (J.1.equivMapOfInjective H.1.subtype H.1.subtype_injective)
      (x ⟨J.1.map H.1.subtype,
        (hXelem (J.1.map H.1.subtype)).2 <|
          isElementary_of_mulEquiv_local
            (J.1.equivMapOfInjective H.1.subtype H.1.subtype_injective)
            (subgroup_isElementary_of_isElementary_local J.1 ((hXelem H.1).1 H.2))⟩)
  let δH : (J : XH) → R(J.1) := fun J ↦
    let JX : X := ⟨J.1.map H.1.subtype,
      (hXelem (J.1.map H.1.subtype)).2 <|
        isElementary_of_mulEquiv_local
          (J.1.equivMapOfInjective H.1.subtype H.1.subtype_injective)
          (subgroup_isElementary_of_isElementary_local J.1 ((hXelem H.1).1 H.2))⟩
    let pJ : elementary_restriction_relation X := ⟨(H, JX), subgroup_chain_map_le_local H.1 J.1⟩
    Subgroup.characterRingTransport
      (J.1.equivMapOfInjective H.1.subtype H.1.subtype_injective)
      (t.1 pJ)
  have hxH : x H = n • y H := by
    -- The global residual-family divisibility theorem already divides the `H`-coordinate by `n`.
    simpa [Pi.smul_apply] using
      (congrArg (fun z : (J : X) → R(J.1) ↦ z H) hy).symm
  have htransported :
      ((Representation.characterRingRestriction XH).toLinearMap (x H)) - ψH = n • δH :=
    transported_subgroup_family_defect_eq_zsmul X hXelem hdx H
  have hsplit :
      x H = sH ψH + n • sH δH :=
    local_coordinate_eq_top_local_image_add_zsmul_of_transported_defect XH sH hsH htransported
  have hpair_y_int :
      ⟪((1 : R(H.1)) : H.1 → ℂ), ((y H : R(H.1)) : H.1 → ℂ)⟫ ∈
        Set.range (algebraMap ℤ ℂ) :=
    pairing_mem_range_int_of_mem_characterRing_with_linear_character_local
      (η := y H) (χ := (1 : H.1 →* ℂˣ))
  rcases hpair_y_int with ⟨b₁, hb₁⟩
  have hpair_x :
      ⟪((1 : R(H.1)) : H.1 → ℂ), ((x H : R(H.1)) : H.1 → ℂ)⟫ =
        algebraMap ℤ ℂ (n * b₁) := by
    -- Since the ambient coordinate is itself `n • y H`, its trivial-line pairing is an
    -- explicit `n`-multiple.
    calc
      ⟪((1 : R(H.1)) : H.1 → ℂ), ((x H : R(H.1)) : H.1 → ℂ)⟫ =
          ⟪((1 : R(H.1)) : H.1 → ℂ), ((n • y H : R(H.1)) : H.1 → ℂ)⟫ := by
            rw [hxH]
      _ = (n : ℂ) * ⟪((1 : R(H.1)) : H.1 → ℂ), ((y H : R(H.1)) : H.1 → ℂ)⟫ := by
            simpa [zsmul_eq_mul] using
              (Representation.groupFunctionPairing_smul_right
                (a := (n : ℂ))
                (φ := (((1 : R(H.1)) : R(H.1)) : H.1 → ℂ))
                (ψ := ((y H : R(H.1)) : H.1 → ℂ))).symm
      _ = (n : ℂ) * algebraMap ℤ ℂ b₁ := by rw [hb₁]
      _ = algebraMap ℤ ℂ (n * b₁) := by simp [Int.cast_mul]
  have hpair_delta_int :
      ⟪((1 : R(H.1)) : H.1 → ℂ), ((sH δH : R(H.1)) : H.1 → ℂ)⟫ ∈
        Set.range (algebraMap ℤ ℂ) :=
    pairing_mem_range_int_of_mem_characterRing_with_linear_character_local
      (η := sH δH) (χ := (1 : H.1 →* ℂˣ))
  rcases hpair_delta_int with ⟨a, ha⟩
  have hpair_split :
      ⟪((1 : R(H.1)) : H.1 → ℂ), ((x H : R(H.1)) : H.1 → ℂ)⟫ =
        ⟪((1 : R(H.1)) : H.1 → ℂ), ((sH ψH : R(H.1)) : H.1 → ℂ)⟫ +
          algebraMap ℤ ℂ (n * a) := by
    -- The local transport identity expresses the top local image as the ambient coordinate minus
    -- an explicit `n`-multiple correction term.
    calc
      ⟪((1 : R(H.1)) : H.1 → ℂ), ((x H : R(H.1)) : H.1 → ℂ)⟫ =
          ⟪((1 : R(H.1)) : H.1 → ℂ), ((sH ψH + n • sH δH : R(H.1)) : H.1 → ℂ)⟫ := by
            rw [hsplit]
      _ =
          ⟪((1 : R(H.1)) : H.1 → ℂ), ((sH ψH : R(H.1)) : H.1 → ℂ)⟫ +
            ⟪((1 : R(H.1)) : H.1 → ℂ), ((n • sH δH : R(H.1)) : H.1 → ℂ)⟫ := by
              exact
                Representation.groupFunctionPairing_add_right
                  (((1 : R(H.1)) : R(H.1)) : H.1 → ℂ)
                  ((sH ψH : R(H.1)) : H.1 → ℂ)
                  ((n • sH δH : R(H.1)) : H.1 → ℂ)
      _ =
          ⟪((1 : R(H.1)) : H.1 → ℂ), ((sH ψH : R(H.1)) : H.1 → ℂ)⟫ +
            (n : ℂ) * ⟪((1 : R(H.1)) : H.1 → ℂ), ((sH δH : R(H.1)) : H.1 → ℂ)⟫ := by
              simp [Representation.groupFunctionPairing_smul_right, zsmul_eq_mul]
      _ =
          ⟪((1 : R(H.1)) : H.1 → ℂ), ((sH ψH : R(H.1)) : H.1 → ℂ)⟫ +
            algebraMap ℤ ℂ (n * a) := by
              rw [ha]
              simp [Int.cast_mul]
  refine ⟨b₁ - a, ?_⟩
  have hsum :
      ⟪((1 : R(H.1)) : H.1 → ℂ), ((sH ψH : R(H.1)) : H.1 → ℂ)⟫ +
          algebraMap ℤ ℂ (n * a) =
        algebraMap ℤ ℂ (n * b₁) := by
    calc
      ⟪((1 : R(H.1)) : H.1 → ℂ), ((sH ψH : R(H.1)) : H.1 → ℂ)⟫ +
          algebraMap ℤ ℂ (n * a) =
        ⟪((1 : R(H.1)) : H.1 → ℂ), ((x H : R(H.1)) : H.1 → ℂ)⟫ := by
          symm
          exact hpair_split
      _ = algebraMap ℤ ℂ (n * b₁) := hpair_x
  have hsub :
      ⟪((1 : R(H.1)) : H.1 → ℂ), ((sH ψH : R(H.1)) : H.1 → ℂ)⟫ =
        algebraMap ℤ ℂ (n * b₁) - algebraMap ℤ ℂ (n * a) :=
    eq_sub_iff_add_eq.mpr hsum
  -- Subtract the correction term to recover the actual top-local trivial-line witness.
  simpa [Int.cast_mul, Int.cast_sub, sub_eq_add_neg, mul_add, mul_assoc, add_comm, add_left_comm,
    add_assoc] using hsub

/-- Helper for Remark 11-11.1-3: in the trivial ambient branch, the singleton local family should
already force the trivial-line pairing against the top local image to be an `n`-multiple. -/
private theorem local_trivial_coordinate_pairing_divisible_of_defect_multiple
    (X : Finset (Subgroup G))
    (hXelem : ∀ H : Subgroup G, H ∈ X ↔ IsElementary H)
    (s : ((H : X) → R(H.1)) →ₗ[ℤ] R(G))
    (hs : Function.LeftInverse s (Representation.characterRingRestriction X).toLinearMap)
    {x : (H : X) → R(H.1)} {t : elementary_coherence_target X hXelem} {n : ℤ}
    (hn : n ≠ 0)
    (hx : s x = 0)
    (hdx : elementary_coherence_defect X hXelem x = n • t)
    (H : X)
    (sH : ((J : (Finset.univ : Finset (Subgroup H.1))) → R(J.1)) →ₗ[ℤ] R(H.1))
    (hsH : Function.LeftInverse sH
      (Representation.characterRingRestriction (Finset.univ : Finset (Subgroup H.1))).toLinearMap)
    (htrivial : (⊥ : Subgroup H.1) = ⊤) :
    let XH : Finset (Subgroup H.1) := Finset.univ
    let ψH : (J : XH) → R(J.1) := fun J ↦
      Subgroup.characterRingTransport
        (J.1.equivMapOfInjective H.1.subtype H.1.subtype_injective)
        (x ⟨J.1.map H.1.subtype,
          (hXelem (J.1.map H.1.subtype)).2 <|
            isElementary_of_mulEquiv_local
              (J.1.equivMapOfInjective H.1.subtype H.1.subtype_injective)
              (subgroup_isElementary_of_isElementary_local J.1 ((hXelem H.1).1 H.2))⟩)
    ∃ b₀ : ℤ,
      ⟪((1 : R(H.1)) : H.1 → ℂ), ((sH ψH : R(H.1)) : H.1 → ℂ)⟫ =
        algebraMap ℤ ℂ (n * b₀) := by
  -- Route correction: the singleton collapse only identifies the local image; the real divisibility
  -- input comes from the global residual-family factorization `x = n • y`.
  simpa using
    top_local_trivial_pairing_divisible_of_residual_family
      X hXelem s hs hn hx hdx H sH hsH

/-- Helper for Remark 11-11.1-3: once every quotient-character difference for a fixed coatom is
an `n`-multiple, the coatom identity already shows that the `M.index`-scaled trivial-line pairing
is an `n`-multiple. -/
private theorem finset_sum_int_multiples
    {ι : Type*} (s : Finset ι) {f : ι → ℂ} {n : ℤ}
    (hdiv : ∀ i ∈ s, ∃ b : ℤ, f i = algebraMap ℤ ℂ (n * b)) :
    ∃ bΣ : ℤ, ∑ i in s, f i = algebraMap ℤ ℂ (n * bΣ) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      refine ⟨0, ?_⟩
      simp
  | @insert a s ha hs =>
      obtain ⟨ba, hba⟩ := hdiv a (by simp [ha])
      obtain ⟨bΣ, hbΣ⟩ := hs fun i hi ↦ hdiv i (by simp [hi, ha])
      refine ⟨ba + bΣ, ?_⟩
      -- Peel off the distinguished summand and combine the two displayed `n`-multiples.
      calc
        ∑ i in Finset.insert a s, f i = f a + ∑ i in s, f i := by simp [ha]
        _ = algebraMap ℤ ℂ (n * ba) + algebraMap ℤ ℂ (n * bΣ) := by rw [hba, hbΣ]
        _ = algebraMap ℤ ℂ ((n * ba) + (n * bΣ)) := by simp [Int.cast_add]
        _ = algebraMap ℤ ℂ (n * (ba + bΣ)) := by
            congr 1
            ring

/-- Helper for Remark 11-11.1-3: once every quotient-character difference for a fixed coatom is
an `n`-multiple, the coatom identity already shows that the `M.index`-scaled trivial-line pairing
is an `n`-multiple. -/
private theorem coatom_index_smul_trivial_line_pairing_divisible_of_fixed_coatom
    {H0 : Type*} [Group H0] [Finite H0] {n : ℤ}
    (M : Subgroup H0) [M.Normal]
    [Fintype ((H0 ⧸ M) →* ℂˣ)]
    (ξH : R(H0))
    (hMpair :
      ∃ bM : ℤ,
        ⟪(Subgroup.characterRingInduction M (1 : R(M)) : H0 → ℂ), (ξH : H0 → ℂ)⟫ =
          algebraMap ℤ ℂ (n * bM))
    (hpair_rewrite :
      ⟪(Subgroup.characterRingInduction M (1 : R(M)) : H0 → ℂ), (ξH : H0 → ℂ)⟫ =
        (M.index : ℂ) * ⟪((1 : R(H0)) : H0 → ℂ), (ξH : H0 → ℂ)⟫ +
          ∑ β : (H0 ⧸ M) →* ℂˣ,
            ⟪((((β.comp (QuotientGroup.mk' M)).toCharacterRing - 1 : R(H0)) : H0 → ℂ),
                (ξH : H0 → ℂ)⟫)
    (hquotdiff :
      ∀ β : (H0 ⧸ M) →* ℂˣ,
        ∃ bβ : ℤ,
            ⟪((((β.comp (QuotientGroup.mk' M)).toCharacterRing - 1 : R(H0)) : H0 → ℂ),
                (ξH : H0 → ℂ)⟫ =
            algebraMap ℤ ℂ (n * bβ)) :
    ∃ b₀ : ℤ,
      (M.index : ℂ) * ⟪((1 : R(H0)) : H0 → ℂ), (ξH : H0 → ℂ)⟫ =
        algebraMap ℤ ℂ (n * b₀) := by
  classical
  rcases hMpair with ⟨bM, hbM⟩
  have hquot_sum :
      ∑ β : (H0 ⧸ M) →* ℂˣ,
          ⟪((((β.comp (QuotientGroup.mk' M)).toCharacterRing - 1 : R(H0)) : H0 → ℂ),
              (ξH : H0 → ℂ)⟫ =
        algebraMap ℤ ℂ (n * bΣ) := by
    -- Package the whole quotient-character family into one arithmetic witness before subtracting
    -- it from the coatom identity.
    exact
      finset_sum_int_multiples
        (s := Finset.univ)
        (f := fun β : (H0 ⧸ M) →* ℂˣ ↦
          ⟪((((β.comp (QuotientGroup.mk' M)).toCharacterRing - 1 : R(H0)) : H0 → ℂ),
              (ξH : H0 → ℂ)⟫)
        (n := n)
        (fun β _ ↦ hquotdiff β)
  rcases hquot_sum with ⟨bΣ, hbΣ⟩
  refine ⟨bM - bΣ, ?_⟩
  have hscaled :
      (M.index : ℂ) * ⟪((1 : R(H0)) : H0 → ℂ), (ξH : H0 → ℂ)⟫ =
        ⟪(Subgroup.characterRingInduction M (1 : R(M)) : H0 → ℂ), (ξH : H0 → ℂ)⟫ -
          ∑ β : (H0 ⧸ M) →* ℂˣ,
            ⟪((((β.comp (QuotientGroup.mk' M)).toCharacterRing - 1 : R(H0)) : H0 → ℂ),
                (ξH : H0 → ℂ)⟫ := by
    exact eq_sub_iff_add_eq.mpr hpair_rewrite.symm
  calc
    (M.index : ℂ) * ⟪((1 : R(H0)) : H0 → ℂ), (ξH : H0 → ℂ)⟫ =
        ⟪(Subgroup.characterRingInduction M (1 : R(M)) : H0 → ℂ), (ξH : H0 → ℂ)⟫ -
          ∑ β : (H0 ⧸ M) →* ℂˣ,
            ⟪((((β.comp (QuotientGroup.mk' M)).toCharacterRing - 1 : R(H0)) : H0 → ℂ),
                (ξH : H0 → ℂ)⟫ := hscaled
    _ = algebraMap ℤ ℂ (n * bM) -
          algebraMap ℤ ℂ (n * bΣ) := by
            rw [hbM, hquot_sum]
    _ = algebraMap ℤ ℂ (n * (bM - bΣ)) := by
            simp [Int.cast_mul, Int.cast_sub, sub_eq_add_neg, mul_add, mul_assoc]

/-- Helper for Remark 11-11.1-3: for a fixed coatom quotient, the coatom step should return the
full top-local package. The quotient-character arithmetic controls the trivial line, while the
nontrivial top characters are supplied separately by the kernel-recursion branch. -/
private theorem coatom_top_local_pairing_divisible_package_of_fixed_coatom
    {H0 : Type*} [Group H0] [Finite H0] {n : ℤ}
    (M : Subgroup H0) [M.Normal]
    (hcomm : ∀ a b : H0 ⧸ M, a * b = b * a)
    [Fintype ((H0 ⧸ M) →* ℂˣ)]
    (ξH : R(H0))
    (hMpair :
      ∃ bM : ℤ,
        ⟪(Subgroup.characterRingInduction M (1 : R(M)) : H0 → ℂ), (ξH : H0 → ℂ)⟫ =
          algebraMap ℤ ℂ (n * bM))
    (hpair_rewrite :
      ⟪(Subgroup.characterRingInduction M (1 : R(M)) : H0 → ℂ), (ξH : H0 → ℂ)⟫ =
        (M.index : ℂ) * ⟪((1 : R(H0)) : H0 → ℂ), (ξH : H0 → ℂ)⟫ +
          ∑ β : (H0 ⧸ M) →* ℂˣ,
            ⟪((((β.comp (QuotientGroup.mk' M)).toCharacterRing - 1 : R(H0)) : H0 → ℂ),
                (ξH : H0 → ℂ)⟫)
    (hquotdiff :
      ∀ β : (H0 ⧸ M) →* ℂˣ,
        ∃ bβ : ℤ,
          ⟪((((β.comp (QuotientGroup.mk' M)).toCharacterRing - 1 : R(H0)) : H0 → ℂ),
              (ξH : H0 → ℂ)⟫ =
            algebraMap ℤ ℂ (n * bβ))
    (htopdiff :
      ∀ α : (⊤ : Subgroup H0) →* ℂˣ, α ≠ 1 →
        ∃ b : ℤ,
          ⟪((Subgroup.characterRingInduction (⊤ : Subgroup H0)
                (α.toCharacterRing - 1) : R(H0)) : H0 → ℂ),
              (ξH : H0 → ℂ)⟫ =
            algebraMap ℤ ℂ (n * b))
    (_hprime : (Nat.card (H0 ⧸ M)).Prime) :
    (∃ b₀ : ℤ,
      (M.index : ℂ) * ⟪((1 : R(H0)) : H0 → ℂ), (ξH : H0 → ℂ)⟫ =
        algebraMap ℤ ℂ (n * b₀)) ∧
      ∀ α : (⊤ : Subgroup H0) →* ℂˣ,
        ∃ b : ℤ,
          ⟪((Subgroup.characterRingInduction (⊤ : Subgroup H0)
                (α.toCharacterRing - 1) : R(H0)) : H0 → ℂ),
              (ξH : H0 → ℂ)⟫ =
            algebraMap ℤ ℂ (n * b) := by
  refine ⟨?_, ?_⟩
  · -- Route correction: the fixed coatom only controls the scaled trivial-line term directly.
    exact
      coatom_index_smul_trivial_line_pairing_divisible_of_fixed_coatom
        M ξH hMpair hpair_rewrite hquotdiff
  · intro α
    by_cases hα : α = 1
    · refine ⟨0, ?_⟩
      -- The trivial top character contributes zero to the difference term.
      subst hα
      simp
    · -- Nontrivial top characters are owned by the separate kernel-recursion branch.
      exact htopdiff α hα

/-- Helper for Remark 11-11.1-3: normalizing the proper-subgroup transport theorem at a kernel
shows that it lands on the induced trivial character from that kernel, not yet on the ambient
top-difference term. This is the precise input expected by the later quotient recursion. -/
private theorem kernel_branch_transport_target_normal_form
    (X : Finset (Subgroup G))
    (hXelem : ∀ H : Subgroup G, H ∈ X ↔ IsElementary H)
    {x : (H : X) → R(H.1)} {t : elementary_coherence_target X hXelem} {n : ℤ}
    (hdx : elementary_coherence_defect X hXelem x = n • t)
    (H : X)
    (sH : ((J : (Finset.univ : Finset (Subgroup H.1))) → R(J.1)) →ₗ[ℤ] R(H.1))
    (hsH : Function.LeftInverse sH
      (Representation.characterRingRestriction (Finset.univ : Finset (Subgroup H.1))).toLinearMap)
    (β : H.1 →* ℂˣ) :
    let XH : Finset (Subgroup H.1) := Finset.univ
    let ψH : (J : XH) → R(J.1) := fun J ↦
      Subgroup.characterRingTransport
        (J.1.equivMapOfInjective H.1.subtype H.1.subtype_injective)
        (x ⟨J.1.map H.1.subtype,
          (hXelem (J.1.map H.1.subtype)).2 <|
            isElementary_of_mulEquiv_local
              (J.1.equivMapOfInjective H.1.subtype H.1.subtype_injective)
              (subgroup_isElementary_of_isElementary_local J.1 ((hXelem H.1).1 H.2))⟩)
    let ξH : R(H.1) := sH ψH
    (let KX : X := ⟨β.ker.map H.1.subtype,
      (hXelem (β.ker.map H.1.subtype)).2 <|
        isElementary_of_mulEquiv_local
          (β.ker.equivMapOfInjective H.1.subtype H.1.subtype_injective)
          (subgroup_isElementary_of_isElementary_local β.ker ((hXelem H.1).1 H.2))⟩
      ∃ c : ℤ, linear_character_pairing_int H.1 β.ker (1 : β.ker →* ℂˣ) (x KX) = n * c) →
      ∃ b : ℤ,
        ⟪(Subgroup.characterRingInduction β.ker (1 : R(β.ker)) : H.1 → ℂ),
            (ξH : H.1 → ℂ)⟫ =
          algebraMap ℤ ℂ (n * b) := by
  classical
  dsimp
  -- This is exactly the proper-subgroup transport theorem specialized at `J = β.ker` and `χ = 1`.
  simpa using
    proper_induced_pairing_divisible_of_transport_pairing_int_divisible
      X hXelem hdx H sH hsH β.ker (1 : β.ker →* ℂˣ)

/-- Helper for Remark 11-11.1-3: a nontrivial ambient linear character stays nontrivial after
factoring through the quotient by its kernel. -/
private theorem kernel_quotient_character_ne_one
    {H0 : Type*} [Group H0]
    (β : H0 →* ℂˣ) (hβ : β ≠ 1) :
    let βq : (H0 ⧸ β.ker) →* ℂˣ :=
      QuotientGroup.lift β.ker β (show β.ker ≤ β.ker from le_rfl)
    βq ≠ 1 := by
  classical
  dsimp
  intro hβq
  apply hβ
  ext x
  -- Read the quotient factorization back along the quotient map to recover the ambient character.
  calc
    β x =
        ((QuotientGroup.lift β.ker β (show β.ker ≤ β.ker from le_rfl)).comp
          (QuotientGroup.mk' β.ker)) x := by
            simpa using
              congrFun
                (QuotientGroup.lift_comp_mk' β.ker β (show β.ker ≤ β.ker from le_rfl)).symm
                x
    _ = 1 := by simp [hβq]

/-- Helper for Remark 11-11.1-3: if an erased quotient character has trivial kernel on the
quotient, then pulling it back along the quotient map does not enlarge the original kernel. -/
private theorem erased_quotient_character_kernel_eq_of_quotient_ker_eq_bot
    {H0 : Type*} [Group H0]
    (β : H0 →* ℂˣ) (γ : (H0 ⧸ β.ker) →* ℂˣ) (hγker : γ.ker = ⊥) :
    (γ.comp (QuotientGroup.mk' β.ker)).ker = β.ker := by
  -- Rewrite both kernels as comaps along the quotient map and collapse the quotient-side kernel
  -- to `⊥`.
  rw [← QuotientGroup.ker_mk' β.ker, ← MonoidHom.comap_ker, hγker, MonoidHom.comap_bot]

/-- Helper for Remark 11-11.1-3: strict kernel growth in the erased quotient-character branch
occurs exactly when the quotient character itself has nontrivial kernel. -/
private theorem erased_quotient_character_kernel_lt_of_quotient_ker_ne_bot
    {H0 : Type*} [Group H0]
    (β : H0 →* ℂˣ) (γ : (H0 ⧸ β.ker) →* ℂˣ) (hγker : γ.ker ≠ ⊥) :
    β.ker < (γ.comp (QuotientGroup.mk' β.ker)).ker := by
  -- Route correction: `γ ≠ βq` does not force strict kernel growth. The correct source-faithful
  -- split is between quotient characters with trivial kernel and those with nontrivial kernel.
  rw [← QuotientGroup.ker_mk' β.ker, ← MonoidHom.comap_ker]
  exact
    (Subgroup.comap_lt_comap_of_surjective (f := QuotientGroup.mk' β.ker)
      (hf := QuotientGroup.mk'_surjective β.ker)).2 <|
      bot_lt_iff_ne_bot.mpr hγker

/-- Helper for Remark 11-11.1-3: isolating the quotient character induced by `β` splits the
kernel-induced pairing into the trivial line, the distinguished ambient difference term, and the
remaining quotient-character differences. -/
private theorem kernel_induced_pairing_decomposes_with_distinguished_difference
    {H0 : Type*} [Group H0] [Finite H0]
    (β : H0 →* ℂˣ) (ξ : R(H0)) :
    let βq : (H0 ⧸ β.ker) →* ℂˣ :=
      QuotientGroup.lift β.ker β (show β.ker ≤ β.ker from le_rfl)
    ⟪(Subgroup.characterRingInduction β.ker (1 : R(β.ker)) : H0 → ℂ), (ξ : H0 → ℂ)⟫ =
      (β.ker.index : ℂ) * ⟪((1 : R(H0)) : H0 → ℂ), (ξ : H0 → ℂ)⟫ +
        ⟪((((β.toCharacterRing - 1 : R(H0)) : H0 → ℂ)), (ξ : H0 → ℂ)⟫ +
          ∑ γ in Finset.univ.erase βq,
            ⟪((((γ.comp (QuotientGroup.mk' β.ker)).toCharacterRing - 1 : R(H0)) : H0 → ℂ),
                (ξ : H0 → ℂ)⟫ := by
  classical
  let e : H0 ⧸ β.ker ≃* β.range := QuotientGroup.quotientKerEquivRange β
  have hcomm : ∀ a b : H0 ⧸ β.ker, a * b = b * a := by
    intro a b
    -- Transport commutativity from the range of `β`, which lies in the commutative group `ℂˣ`.
    apply e.injective
    simp [mul_comm]
  letI : CommGroup (H0 ⧸ β.ker) :=
    { QuotientGroup.Quotient.group β.ker with
      mul_comm := hcomm }
  letI : Fintype ((H0 ⧸ β.ker) →* ℂˣ) := linearCharacterFintype
  let βq : (H0 ⧸ β.ker) →* ℂˣ :=
    QuotientGroup.lift β.ker β (show β.ker ≤ β.ker from le_rfl)
  let term : ((H0 ⧸ β.ker) →* ℂˣ) → ℂ := fun γ ↦
    ⟪((((γ.comp (QuotientGroup.mk' β.ker)).toCharacterRing - 1 : R(H0)) : H0 → ℂ),
        (ξ : H0 → ℂ)⟫
  have hβ_factor : β = βq.comp (QuotientGroup.mk' β.ker) := by
    -- The chosen quotient character is defined precisely by factoring `β` through `β.ker`.
    simpa [βq] using
      (QuotientGroup.lift_comp_mk' β.ker β (show β.ker ≤ β.ker from le_rfl)).symm
  have hsplit :
      ∑ γ : (H0 ⧸ β.ker) →* ℂˣ, term γ =
        term βq + ∑ γ in Finset.univ.erase βq, term γ := by
    -- Isolate the distinguished quotient character from the full quotient-character sum.
    simpa [term] using
      (Finset.sum_erase_add (s := Finset.univ) (a := βq) (by simp)).symm
  have hβq_term :
      term βq =
        ⟪((((β.toCharacterRing - 1 : R(H0)) : H0 → ℂ)), (ξ : H0 → ℂ)⟫ := by
    -- After substituting the quotient factorization, the distinguished quotient summand is the
    -- ambient `β - 1` difference term.
    simpa [term, ← hβ_factor]
  -- Expand the kernel-induced pairing and then split off the distinguished quotient character.
  calc
    ⟪(Subgroup.characterRingInduction β.ker (1 : R(β.ker)) : H0 → ℂ), (ξ : H0 → ℂ)⟫ =
        (β.ker.index : ℂ) * ⟪((1 : R(H0)) : H0 → ℂ), (ξ : H0 → ℂ)⟫ +
          ∑ γ : (H0 ⧸ β.ker) →* ℂˣ, term γ := by
            simpa [term] using
              induced_trivial_pairing_eq_index_trivial_pairing_add_quotient_difference_sum
                (M := β.ker) hcomm (ξ := ξ)
    _ =
        (β.ker.index : ℂ) * ⟪((1 : R(H0)) : H0 → ℂ), (ξ : H0 → ℂ)⟫ +
          (term βq + ∑ γ in Finset.univ.erase βq, term γ) := by
            rw [hsplit]
    _ =
        (β.ker.index : ℂ) * ⟪((1 : R(H0)) : H0 → ℂ), (ξ : H0 → ℂ)⟫ +
          ⟪((((β.toCharacterRing - 1 : R(H0)) : H0 → ℂ)), (ξ : H0 → ℂ)⟫ +
            ∑ γ in Finset.univ.erase βq, term γ := by
              simpa [hβq_term, add_assoc]

/-- Helper for Remark 11-11.1-3: scaling the trivial-line pairing by the kernel index preserves
`n`-divisibility in the kernel-recursion branch. -/
private theorem scaled_top_local_trivial_pairing_divisible_of_residual_family
    (X : Finset (Subgroup G))
    (hXelem : ∀ H : Subgroup G, H ∈ X ↔ IsElementary H)
    (s : ((H : X) → R(H.1)) →ₗ[ℤ] R(G))
    (hs : Function.LeftInverse s (Representation.characterRingRestriction X).toLinearMap)
    {x : (H : X) → R(H.1)} {t : elementary_coherence_target X hXelem} {n : ℤ}
    (hn : n ≠ 0) (hx : s x = 0)
    (hdx : elementary_coherence_defect X hXelem x = n • t)
    (H : X)
    (sH : ((J : (Finset.univ : Finset (Subgroup H.1))) → R(J.1)) →ₗ[ℤ] R(H.1))
    (hsH : Function.LeftInverse sH
      (Representation.characterRingRestriction (Finset.univ : Finset (Subgroup H.1))).toLinearMap)
    (β : H.1 →* ℂˣ) :
    let XH : Finset (Subgroup H.1) := Finset.univ
    let ψH : (J : XH) → R(J.1) := fun J ↦
      Subgroup.characterRingTransport
        (J.1.equivMapOfInjective H.1.subtype H.1.subtype_injective)
        (x ⟨J.1.map H.1.subtype,
          (hXelem (J.1.map H.1.subtype)).2 <|
            isElementary_of_mulEquiv_local
              (J.1.equivMapOfInjective H.1.subtype H.1.subtype_injective)
              (subgroup_isElementary_of_isElementary_local J.1 ((hXelem H.1).1 H.2))⟩)
    ∃ b₀ : ℤ,
      (β.ker.index : ℂ) * ⟪((1 : R(H.1)) : H.1 → ℂ), ((sH ψH : R(H.1)) : H.1 → ℂ)⟫ =
        algebraMap ℤ ℂ (n * b₀) := by
  classical
  dsimp
  obtain ⟨b₀, hb₀⟩ :=
    top_local_trivial_pairing_divisible_of_residual_family
      X hXelem s hs hn hx hdx H sH hsH
  refine ⟨(β.ker.index : ℤ) * b₀, ?_⟩
  -- Multiply the already proved trivial-line witness by the kernel index and fold the result
  -- back into a single `n`-multiple.
  calc
    (β.ker.index : ℂ) * ⟪((1 : R(H.1)) : H.1 → ℂ), ((sH ψH : R(H.1)) : H.1 → ℂ)⟫ =
        algebraMap ℤ ℂ (β.ker.index : ℤ) *
          ⟪((1 : R(H.1)) : H.1 → ℂ), ((sH ψH : R(H.1)) : H.1 → ℂ)⟫ := by
            simp
    _ = algebraMap ℤ ℂ (β.ker.index : ℤ) * algebraMap ℤ ℂ (n * b₀) := by
          rw [hb₀]
    _ = algebraMap ℤ ℂ ((β.ker.index : ℤ) * (n * b₀)) := by
          simp [Int.cast_mul]
    _ = algebraMap ℤ ℂ (n * ((β.ker.index : ℤ) * b₀)) := by
          congr 1
          ring

/-- Helper for Remark 11-11.1-3: once the quotient character induced by `β` is isolated, the
remaining erased quotient-character sum is the only arithmetic package still needed in the kernel
recursion. -/
private theorem erased_quotient_character_difference_divisible_of_comp_eq_one
    (X : Finset (Subgroup G))
    (hXelem : ∀ H : Subgroup G, H ∈ X ↔ IsElementary H)
    {x : (H : X) → R(H.1)} {t : elementary_coherence_target X hXelem} {n : ℤ}
    (H : X)
    (sH : ((J : (Finset.univ : Finset (Subgroup H.1))) → R(J.1)) →ₗ[ℤ] R(H.1))
    (β : H.1 →* ℂˣ)
    (γ : (H.1 ⧸ β.ker) →* ℂˣ)
    (hδ : γ.comp (QuotientGroup.mk' β.ker) = 1) :
    ∃ bγ : ℤ,
      ⟪((((γ.comp (QuotientGroup.mk' β.ker)).toCharacterRing - 1 : R(H.1)) :
            H.1 → ℂ),
          ((sH
              (fun J ↦
                Subgroup.characterRingTransport
                  (J.1.equivMapOfInjective H.1.subtype H.1.subtype_injective)
                  (x ⟨J.1.map H.1.subtype,
                    (hXelem (J.1.map H.1.subtype)).2 <|
                      isElementary_of_mulEquiv_local
                        (J.1.equivMapOfInjective H.1.subtype H.1.subtype_injective)
                        (subgroup_isElementary_of_isElementary_local J.1
                          ((hXelem H.1).1 H.2))⟩)) : R(H.1)) : H.1 → ℂ)⟫ =
        algebraMap ℤ ℂ (n * bγ) := by
  refine ⟨0, ?_⟩
  -- When the lifted quotient character is trivial, the ambient difference character vanishes.
  have hzero :
      (((γ.comp (QuotientGroup.mk' β.ker)).toCharacterRing - 1 : R(H.1))) = 0 := by
    rw [hδ]
    simp
  -- The pairing with the zero difference term is therefore the zero `n`-multiple.
  rw [hzero]
  simp

/-- Helper for Remark 11-11.1-3: a nonfaithful erased quotient character enlarges the ambient
kernel, so the kernel-index measure used in the owner recursion strictly decreases. -/
private theorem kernel_growth_measure_decreases_on_nonfaithful_erased_branch
    {H0 : Type*} [Group H0] [Finite H0]
    (β : H0 →* ℂˣ) (γ : (H0 ⧸ β.ker) →* ℂˣ) (hγker : γ.ker ≠ ⊥) :
    (γ.comp (QuotientGroup.mk' β.ker)).ker.index < β.ker.index := by
  -- Convert the strict kernel inclusion into the strict index decrease needed by strong induction.
  exact
    Subgroup.index_strictAnti
      (erased_quotient_character_kernel_lt_of_quotient_ker_ne_bot β γ hγker)

/-- Helper for Remark 11-11.1-3: on a prime-order quotient, every nontrivial lifted linear
character has kernel exactly the coatom used to form the quotient. -/
private theorem lifted_prime_quotient_character_kernel_eq_coatom
    {H0 : Type*} [Group H0] [Finite H0]
    (M : Subgroup H0) [M.Normal]
    (hprime : (Nat.card (H0 ⧸ M)).Prime)
    (β : (H0 ⧸ M) →* ℂˣ) (hβ : β ≠ 1) :
    (β.comp (QuotientGroup.mk' M)).ker = M := by
  letI : Fact (Nat.card (H0 ⧸ M)).Prime := ⟨hprime⟩
  have hβker_bot : β.ker = ⊥ := by
    rcases Subgroup.eq_bot_or_eq_top_of_prime_card β.ker with hker | hker
    · exact hker
    · exfalso
      apply hβ
      ext x
      have hx : x ∈ β.ker := by
        rw [hker]
        simp
      simpa [MonoidHom.mem_ker] using hx
  ext x
  -- On the quotient, trivial kernel means the only lifted zeros occur on the defining coatom.
  change QuotientGroup.mk' M x ∈ β.ker ↔ x ∈ M
  simpa [hβker_bot] using (Subgroup.quotient_mk'_eq_one_iff M x)

/-- Helper for Remark 11-11.1-3: if the chosen coatom sits strictly above the ambient kernel,
every nontrivial character of the prime quotient lifts to a nontrivial ambient character whose
kernel index is strictly smaller. -/
private theorem lifted_prime_coatom_character_has_smaller_kernel_index
    {H0 : Type*} [Group H0] [Finite H0]
    (δ : H0 →* ℂˣ) (M : Subgroup H0) [M.Normal]
    (hδker_lt_M : δ.ker < M)
    (hprime : (Nat.card (H0 ⧸ M)).Prime)
    (β : (H0 ⧸ M) →* ℂˣ) (hβ : β ≠ 1) :
    let ε : H0 →* ℂˣ := β.comp (QuotientGroup.mk' M)
    ε ≠ 1 ∧ ε.ker = M ∧ ε.ker.index < δ.ker.index := by
  classical
  dsimp
  have hε_ne : β.comp (QuotientGroup.mk' M) ≠ 1 := by
    intro hε
    apply hβ
    ext y
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective M y
    -- Evaluate the lifted equality on a representative of `y` to recover the quotient character.
    simpa using congrFun (congrArg MonoidHom.toFun hε) x
  have hε_ker :
      (β.comp (QuotientGroup.mk' M)).ker = M := by
    -- On the prime quotient, every nontrivial character is faithful, so the pullback kernel is
    -- exactly the coatom used to form the quotient.
    exact lifted_prime_quotient_character_kernel_eq_coatom M hprime β hβ
  refine ⟨hε_ne, hε_ker, ?_⟩
  -- Strict kernel growth translates to strict index decrease along the induction measure.
  simpa [hε_ker] using Subgroup.index_strictAnti hδker_lt_M

/-- Helper for Remark 11-11.1-3: on a prime quotient, the only erased nonfaithful character is the
trivial one, so its ambient difference branch contributes zero. -/
private theorem prime_coatom_nonfaithful_erased_branch_vanishes
    {H0 : Type*} [Group H0] [Finite H0]
    (M : Subgroup H0) [M.Normal]
    (hprime : (Nat.card (H0 ⧸ M)).Prime)
    (β : (H0 ⧸ M) →* ℂˣ) (hβ : β ≠ 1)
    (ξ : R(H0)) :
    ∑ γ in ((Finset.univ.erase β).filter fun γ => γ.ker ≠ ⊥),
      ⟪((((γ.comp (QuotientGroup.mk' M)).toCharacterRing - 1 : R(H0)) : H0 → ℂ),
          (ξ : H0 → ℂ)⟫ = 0 := by
  classical
  have hfilter :
      ((Finset.univ.erase β).filter fun γ => γ.ker ≠ ⊥) =
        ({1} : Finset ((H0 ⧸ M) →* ℂˣ)) := by
    apply Finset.ext
    intro γ
    simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_univ, true_and,
      Finset.mem_singleton]
    constructor
    · intro hγ
      rcases Subgroup.eq_bot_or_eq_top_of_prime_card γ.ker with hγker | hγker
      · exact (hγ.2 hγker).elim
      · ext x
        have hxker : x ∈ γ.ker := by
          rw [hγker]
          simp
        -- Kernel equal to `⊤` means the quotient character is trivial.
        simpa [MonoidHom.mem_ker] using hxker
    · intro hγ
      subst hγ
      constructor
      · simpa [eq_comm] using hβ
      · simp
  -- After identifying the filtered branch with the singleton `{1}`, the difference term is zero.
  rw [hfilter]
  simp

/-- Helper for Remark 11-11.1-3: on a prime quotient, every nontrivial linear character is
faithful, so filtering the erased character family by `ker = ⊥` does not remove any term. -/
private theorem prime_quotient_faithful_filter_eq_erase_one
    {H0 : Type*} [Group H0] [Finite H0]
    (M : Subgroup H0) [M.Normal]
    (hprime : (Nat.card (H0 ⧸ M)).Prime) :
    ((Finset.univ.erase (1 : (H0 ⧸ M) →* ℂˣ)).filter fun γ => γ.ker = ⊥) =
      Finset.univ.erase (1 : (H0 ⧸ M) →* ℂˣ) := by
  classical
  apply Finset.ext
  intro γ
  simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_univ, true_and]
  constructor
  · intro hγ
    refine ⟨?_, hγ.1⟩
    intro hγ_one
    have hγker_top : γ.ker = ⊤ := by
      ext x
      have hxker : γ x = 1 := by simpa [hγ_one]
      simpa [MonoidHom.mem_ker] using hxker
    exact Subgroup.bot_ne_top hγ.2.symm hγker_top
  · intro hγ
    refine ⟨hγ.2, ?_⟩
    rcases Subgroup.eq_bot_or_eq_top_of_prime_card γ.ker with hγker | hγker
    · exact hγker
    · exfalso
      apply hγ.1
      ext x
      have hxker : x ∈ γ.ker := by
        rw [hγker]
        simp
      -- On a prime quotient, kernel `⊤` forces the character to be trivial.
      simpa [MonoidHom.mem_ker] using hxker

/-- Helper for Remark 11-11.1-3: once every nontrivial character of the prime quotient `H0 ⧸ M`
has an `n`-divisible lifted difference pairing, the whole faithful lifted quotient block is an
`n`-multiple. This isolates the arithmetic part of the strict coatom branch from the remaining
reassembly identity. -/
private theorem prime_quotient_faithful_lift_difference_sum_divisible
    {H0 : Type*} [Group H0] [Finite H0] {n : ℤ}
    (M : Subgroup H0) [M.Normal]
    (hprime : (Nat.card (H0 ⧸ M)).Prime)
    (ξH : R(H0))
    (hquotdiff :
      ∀ β : (H0 ⧸ M) →* ℂˣ, β ≠ 1 →
        ∃ bβ : ℤ,
          ⟪((((β.comp (QuotientGroup.mk' M)).toCharacterRing - 1 : R(H0)) : H0 → ℂ),
              (ξH : H0 → ℂ)⟫ =
            algebraMap ℤ ℂ (n * bβ)) :
    ∃ bΣ : ℤ,
      ∑ β in ((Finset.univ.erase (1 : (H0 ⧸ M) →* ℂˣ)).filter fun β => β.ker = ⊥),
        ⟪((((β.comp (QuotientGroup.mk' M)).toCharacterRing - 1 : R(H0)) : H0 → ℂ),
            (ξH : H0 → ℂ)⟫ =
        algebraMap ℤ ℂ (n * bΣ) := by
  classical
  obtain ⟨bΣ, hbΣ⟩ :=
    finset_sum_int_multiples
      (s := Finset.univ.erase (1 : (H0 ⧸ M) →* ℂˣ))
      (f := fun β : (H0 ⧸ M) →* ℂˣ ↦
        ⟪((((β.comp (QuotientGroup.mk' M)).toCharacterRing - 1 : R(H0)) : H0 → ℂ),
            (ξH : H0 → ℂ)⟫)
      (n := n) fun β hβ ↦ by
        -- On the erased quotient family, membership is exactly the nontriviality needed to call
        -- the strict-branch lift hypothesis.
        exact hquotdiff β (by simpa [Finset.mem_erase] using hβ)
  -- On a prime quotient the faithful filter is redundant, so the packaged finite sum already has
  -- the target shape.
  refine ⟨bΣ, ?_⟩
  simpa [prime_quotient_faithful_filter_eq_erase_one (M := M) hprime] using hbΣ

/-- Helper for Remark 11-11.1-3: if the chosen coatom already equals the kernel, then the coatom
identity reduces the faithful cyclic layer to the coatom induced-trivial pairing minus the
distinguished ambient difference term. -/
private theorem faithful_cyclic_layer_of_kernel_eq_chosen_coatom_of_difference_divisible
    {H0 : Type*} [Group H0] [Finite H0] {n : ℤ}
    (δ : H0 →* ℂˣ) (hδ : δ ≠ 1)
    (M : Subgroup H0) [M.Normal]
    (ξH : R(H0))
    (hEq : δ.ker = M)
    (hprime : (Nat.card (H0 ⧸ M)).Prime)
    (hMpair :
      ∃ bM : ℤ,
        ⟪(Subgroup.characterRingInduction M (1 : R(M)) : H0 → ℂ), (ξH : H0 → ℂ)⟫ =
          algebraMap ℤ ℂ (n * bM))
    (hdiff :
      ∃ bδ : ℤ,
        ⟪((((δ.toCharacterRing - 1 : R(H0)) : H0 → ℂ)), (ξH : H0 → ℂ)⟫ =
          algebraMap ℤ ℂ (n * bδ)) :
    ∃ bC : ℤ,
      (δ.ker.index : ℂ) * ⟪((1 : R(H0)) : H0 → ℂ), (ξH : H0 → ℂ)⟫ +
        ∑ γ in ((Finset.univ.erase
            (QuotientGroup.lift δ.ker δ (show δ.ker ≤ δ.ker from le_rfl))).filter
          fun γ => γ.ker = ⊥),
          ⟪((((γ.comp (QuotientGroup.mk' δ.ker)).toCharacterRing - 1 : R(H0)) :
                H0 → ℂ),
              (ξH : H0 → ℂ)⟫ =
        algebraMap ℤ ℂ (n * bC) := by
  classical
  subst hEq
  let δq : (H0 ⧸ δ.ker) →* ℂˣ :=
    QuotientGroup.lift δ.ker δ (show δ.ker ≤ δ.ker from le_rfl)
  let term : ((H0 ⧸ δ.ker) →* ℂˣ) → ℂ := fun γ ↦
    ⟪((((γ.comp (QuotientGroup.mk' δ.ker)).toCharacterRing - 1 : R(H0)) : H0 → ℂ),
        (ξH : H0 → ℂ)⟫
  obtain ⟨_, hδq_ne, _, _⟩ := kernel_quotient_distinguished_character_data δ hδ
  rcases hMpair with ⟨bM, hbM⟩
  rcases hdiff with ⟨bδ, hbδ⟩
  have hsplit :
      ∑ γ in Finset.univ.erase δq, term γ =
        ∑ γ in ((Finset.univ.erase δq).filter fun γ => γ.ker = ⊥), term γ +
          ∑ γ in ((Finset.univ.erase δq).filter fun γ => γ.ker ≠ ⊥), term γ := by
    -- Split the erased quotient-character family into faithful and nonfaithful branches.
    simpa using
      (Finset.sum_filter_add_sum_filter_not
        (s := Finset.univ.erase δq)
        (f := term)
        (p := fun γ : (H0 ⧸ δ.ker) →* ℂˣ => γ.ker = ⊥)).symm
  have hnonfaithful :
      ∑ γ in ((Finset.univ.erase δq).filter fun γ => γ.ker ≠ ⊥), term γ = 0 := by
    -- On the prime quotient above the chosen coatom, the only erased nonfaithful term is the
    -- trivial character, so its ambient difference contribution vanishes.
    simpa [δq, term] using
      prime_coatom_nonfaithful_erased_branch_vanishes
        (M := δ.ker) hprime δq hδq_ne ξH
  have hrewrite :
      ⟪(Subgroup.characterRingInduction δ.ker (1 : R(δ.ker)) : H0 → ℂ), (ξH : H0 → ℂ)⟫ =
        ((δ.ker.index : ℂ) * ⟪((1 : R(H0)) : H0 → ℂ), (ξH : H0 → ℂ)⟫ +
            ∑ γ in ((Finset.univ.erase δq).filter fun γ => γ.ker = ⊥), term γ) +
          ⟪((((δ.toCharacterRing - 1 : R(H0)) : H0 → ℂ)), (ξH : H0 → ℂ)⟫ := by
    -- Rewrite the coatom induced-trivial pairing by isolating the faithful erased branch and then
    -- discard the prime-quotient nonfaithful branch.
    calc
      ⟪(Subgroup.characterRingInduction δ.ker (1 : R(δ.ker)) : H0 → ℂ), (ξH : H0 → ℂ)⟫ =
          (δ.ker.index : ℂ) * ⟪((1 : R(H0)) : H0 → ℂ), (ξH : H0 → ℂ)⟫ +
            ⟪((((δ.toCharacterRing - 1 : R(H0)) : H0 → ℂ)), (ξH : H0 → ℂ)⟫ +
              ∑ γ in Finset.univ.erase δq, term γ := by
                simpa [δq, term] using
                  kernel_induced_pairing_decomposes_with_distinguished_difference
                    (β := δ)
                    (ξ := ξH)
      _ =
          (δ.ker.index : ℂ) * ⟪((1 : R(H0)) : H0 → ℂ), (ξH : H0 → ℂ)⟫ +
            ⟪((((δ.toCharacterRing - 1 : R(H0)) : H0 → ℂ)), (ξH : H0 → ℂ)⟫ +
              (∑ γ in ((Finset.univ.erase δq).filter fun γ => γ.ker = ⊥), term γ +
                ∑ γ in ((Finset.univ.erase δq).filter fun γ => γ.ker ≠ ⊥), term γ) := by
                  rw [hsplit]
      _ =
          (δ.ker.index : ℂ) * ⟪((1 : R(H0)) : H0 → ℂ), (ξH : H0 → ℂ)⟫ +
            ⟪((((δ.toCharacterRing - 1 : R(H0)) : H0 → ℂ)), (ξH : H0 → ℂ)⟫ +
              ∑ γ in ((Finset.univ.erase δq).filter fun γ => γ.ker = ⊥), term γ := by
                  rw [hnonfaithful]
                  simp
      _ =
          ((δ.ker.index : ℂ) * ⟪((1 : R(H0)) : H0 → ℂ), (ξH : H0 → ℂ)⟫ +
              ∑ γ in ((Finset.univ.erase δq).filter fun γ => γ.ker = ⊥), term γ) +
            ⟪((((δ.toCharacterRing - 1 : R(H0)) : H0 → ℂ)), (ξH : H0 → ℂ)⟫ := by
                  abel
  have htarget :
      (δ.ker.index : ℂ) * ⟪((1 : R(H0)) : H0 → ℂ), (ξH : H0 → ℂ)⟫ +
          ∑ γ in ((Finset.univ.erase δq).filter fun γ => γ.ker = ⊥), term γ =
        ⟪(Subgroup.characterRingInduction δ.ker (1 : R(δ.ker)) : H0 → ℂ), (ξH : H0 → ℂ)⟫ -
          ⟪((((δ.toCharacterRing - 1 : R(H0)) : H0 → ℂ)), (ξH : H0 → ℂ)⟫ := by
    -- Move the distinguished difference term to the right to isolate the faithful cyclic layer.
    exact eq_sub_iff_add_eq.mpr <| by
      simpa [add_comm, add_left_comm, add_assoc] using hrewrite.symm
  refine ⟨bM - bδ, ?_⟩
  -- Combine the coatom induced-trivial witness with the distinguished-difference witness by
  -- subtraction.
  calc
    (δ.ker.index : ℂ) * ⟪((1 : R(H0)) : H0 → ℂ), (ξH : H0 → ℂ)⟫ +
        ∑ γ in ((Finset.univ.erase δq).filter fun γ => γ.ker = ⊥), term γ =
      ⟪(Subgroup.characterRingInduction δ.ker (1 : R(δ.ker)) : H0 → ℂ), (ξH : H0 → ℂ)⟫ -
        ⟪((((δ.toCharacterRing - 1 : R(H0)) : H0 → ℂ)), (ξH : H0 → ℂ)⟫ := htarget
    _ = algebraMap ℤ ℂ (n * bM) - algebraMap ℤ ℂ (n * bδ) := by
          rw [hbM, hbδ]
    _ = algebraMap ℤ ℂ (n * (bM - bδ)) := by
          simp [Int.cast_mul, Int.cast_sub, sub_eq_add_neg, mul_add, mul_assoc]

/-- Helper for Remark 11-11.1-3: the same chosen-coatom identity can be read in reverse. If the
coatom induced-trivial pairing and the faithful cyclic layer are both `n`-multiples, then the
distinguished ambient difference term is an `n`-multiple as well. -/
private theorem difference_divisible_of_kernel_eq_chosen_coatom_of_faithful_cyclic_layer_divisible
    {H0 : Type*} [Group H0] [Finite H0] {n : ℤ}
    (δ : H0 →* ℂˣ) (hδ : δ ≠ 1)
    (M : Subgroup H0) [M.Normal]
    (ξH : R(H0))
    (hEq : δ.ker = M)
    (hprime : (Nat.card (H0 ⧸ M)).Prime)
    (hMpair :
      ∃ bM : ℤ,
        ⟪(Subgroup.characterRingInduction M (1 : R(M)) : H0 → ℂ), (ξH : H0 → ℂ)⟫ =
          algebraMap ℤ ℂ (n * bM))
    (hcyclic :
      ∃ bC : ℤ,
        (δ.ker.index : ℂ) * ⟪((1 : R(H0)) : H0 → ℂ), (ξH : H0 → ℂ)⟫ +
          ∑ γ in ((Finset.univ.erase
              (QuotientGroup.lift δ.ker δ (show δ.ker ≤ δ.ker from le_rfl))).filter
            fun γ => γ.ker = ⊥),
            ⟪((((γ.comp (QuotientGroup.mk' δ.ker)).toCharacterRing - 1 : R(H0)) :
                  H0 → ℂ),
                (ξH : H0 → ℂ)⟫ =
          algebraMap ℤ ℂ (n * bC)) :
    ∃ bδ : ℤ,
      ⟪((((δ.toCharacterRing - 1 : R(H0)) : H0 → ℂ)), (ξH : H0 → ℂ)⟫ =
        algebraMap ℤ ℂ (n * bδ) := by
  classical
  subst hEq
  let δq : (H0 ⧸ δ.ker) →* ℂˣ :=
    QuotientGroup.lift δ.ker δ (show δ.ker ≤ δ.ker from le_rfl)
  let term : ((H0 ⧸ δ.ker) →* ℂˣ) → ℂ := fun γ ↦
    ⟪((((γ.comp (QuotientGroup.mk' δ.ker)).toCharacterRing - 1 : R(H0)) : H0 → ℂ),
        (ξH : H0 → ℂ)⟫
  obtain ⟨_, hδq_ne, _, _⟩ := kernel_quotient_distinguished_character_data δ hδ
  rcases hMpair with ⟨bM, hbM⟩
  rcases hcyclic with ⟨bC, hbC⟩
  have hsplit :
      ∑ γ in Finset.univ.erase δq, term γ =
        ∑ γ in ((Finset.univ.erase δq).filter fun γ => γ.ker = ⊥), term γ +
          ∑ γ in ((Finset.univ.erase δq).filter fun γ => γ.ker ≠ ⊥), term γ := by
    -- Split the erased quotient-character family into faithful and nonfaithful branches.
    simpa using
      (Finset.sum_filter_add_sum_filter_not
        (s := Finset.univ.erase δq)
        (f := term)
        (p := fun γ : (H0 ⧸ δ.ker) →* ℂˣ => γ.ker = ⊥)).symm
  have hnonfaithful :
      ∑ γ in ((Finset.univ.erase δq).filter fun γ => γ.ker ≠ ⊥), term γ = 0 := by
    -- On the prime quotient above the chosen coatom, the erased nonfaithful branch still vanishes.
    simpa [δq, term] using
      prime_coatom_nonfaithful_erased_branch_vanishes
        (M := δ.ker) hprime δq hδq_ne ξH
  have hrewrite :
      ⟪(Subgroup.characterRingInduction δ.ker (1 : R(δ.ker)) : H0 → ℂ), (ξH : H0 → ℂ)⟫ =
        ((δ.ker.index : ℂ) * ⟪((1 : R(H0)) : H0 → ℂ), (ξH : H0 → ℂ)⟫ +
            ∑ γ in ((Finset.univ.erase δq).filter fun γ => γ.ker = ⊥), term γ) +
          ⟪((((δ.toCharacterRing - 1 : R(H0)) : H0 → ℂ)), (ξH : H0 → ℂ)⟫ := by
    -- Rewrite the coatom induced-trivial pairing by isolating the faithful erased branch and then
    -- discard the prime-quotient nonfaithful branch.
    calc
      ⟪(Subgroup.characterRingInduction δ.ker (1 : R(δ.ker)) : H0 → ℂ), (ξH : H0 → ℂ)⟫ =
          (δ.ker.index : ℂ) * ⟪((1 : R(H0)) : H0 → ℂ), (ξH : H0 → ℂ)⟫ +
            ⟪((((δ.toCharacterRing - 1 : R(H0)) : H0 → ℂ)), (ξH : H0 → ℂ)⟫ +
              ∑ γ in Finset.univ.erase δq, term γ := by
                simpa [δq, term] using
                  kernel_induced_pairing_decomposes_with_distinguished_difference
                    (β := δ)
                    (ξ := ξH)
      _ =
          (δ.ker.index : ℂ) * ⟪((1 : R(H0)) : H0 → ℂ), (ξH : H0 → ℂ)⟫ +
            ⟪((((δ.toCharacterRing - 1 : R(H0)) : H0 → ℂ)), (ξH : H0 → ℂ)⟫ +
              (∑ γ in ((Finset.univ.erase δq).filter fun γ => γ.ker = ⊥), term γ +
                ∑ γ in ((Finset.univ.erase δq).filter fun γ => γ.ker ≠ ⊥), term γ) := by
                  rw [hsplit]
      _ =
          (δ.ker.index : ℂ) * ⟪((1 : R(H0)) : H0 → ℂ), (ξH : H0 → ℂ)⟫ +
            ⟪((((δ.toCharacterRing - 1 : R(H0)) : H0 → ℂ)), (ξH : H0 → ℂ)⟫ +
              ∑ γ in ((Finset.univ.erase δq).filter fun γ => γ.ker = ⊥), term γ := by
                  rw [hnonfaithful]
                  simp
      _ =
          ((δ.ker.index : ℂ) * ⟪((1 : R(H0)) : H0 → ℂ), (ξH : H0 → ℂ)⟫ +
              ∑ γ in ((Finset.univ.erase δq).filter fun γ => γ.ker = ⊥), term γ) +
            ⟪((((δ.toCharacterRing - 1 : R(H0)) : H0 → ℂ)), (ξH : H0 → ℂ)⟫ := by
                  abel
  have htarget :
      ⟪((((δ.toCharacterRing - 1 : R(H0)) : H0 → ℂ)), (ξH : H0 → ℂ)⟫ =
        ⟪(Subgroup.characterRingInduction δ.ker (1 : R(δ.ker)) : H0 → ℂ), (ξH : H0 → ℂ)⟫ -
          ((δ.ker.index : ℂ) * ⟪((1 : R(H0)) : H0 → ℂ), (ξH : H0 → ℂ)⟫ +
            ∑ γ in ((Finset.univ.erase δq).filter fun γ => γ.ker = ⊥), term γ) := by
    -- Move the faithful cyclic layer to the right to isolate the distinguished difference term.
    exact eq_sub_iff_add_eq.mpr <| by
      simpa [add_comm, add_left_comm, add_assoc] using hrewrite.symm
  refine ⟨bM - bC, ?_⟩
  -- Subtract the faithful cyclic-layer witness from the coatom induced-trivial witness.
  calc
    ⟪((((δ.toCharacterRing - 1 : R(H0)) : H0 → ℂ)), (ξH : H0 → ℂ)⟫ =
      ⟪(Subgroup.characterRingInduction δ.ker (1 : R(δ.ker)) : H0 → ℂ), (ξH : H0 → ℂ)⟫ -
        ((δ.ker.index : ℂ) * ⟪((1 : R(H0)) : H0 → ℂ), (ξH : H0 → ℂ)⟫ +
          ∑ γ in ((Finset.univ.erase δq).filter fun γ => γ.ker = ⊥), term γ) := htarget
    _ = algebraMap ℤ ℂ (n * bM) - algebraMap ℤ ℂ (n * bC) := by
          rw [hbM, hbC]
    _ = algebraMap ℤ ℂ (n * (bM - bC)) := by
          simp [Int.cast_mul, Int.cast_sub, sub_eq_add_neg, mul_add, mul_assoc]

/-- Helper for Remark 11-11.1-3: if `δ.ker < M` and `β` is a nontrivial character of the prime
coatom quotient `H0 ⧸ M`, then the smaller-kernel package for the lift `β.comp mk' M` already
supplies the ambient difference-pairing divisibility witness needed in the strict branch. -/
private theorem prime_coatom_lift_difference_pairing_divisible_from_smaller_kernel_package
    {H0 : Type*} [Group H0] [Finite H0] {n : ℤ}
    (δ : H0 →* ℂˣ)
    (M : Subgroup H0) [M.Normal]
    (hδker_lt_M : δ.ker < M)
    (hprime : (Nat.card (H0 ⧸ M)).Prime)
    (ξH : R(H0))
    (hMpair :
      ∃ bM : ℤ,
        ⟪(Subgroup.characterRingInduction M (1 : R(M)) : H0 → ℂ), (ξH : H0 → ℂ)⟫ =
          algebraMap ℤ ℂ (n * bM))
    (hm :
      ∀ ε : H0 →* ℂˣ, ε ≠ 1 → ε.ker.index < δ.ker.index →
        ∃ bC : ℤ,
          (ε.ker.index : ℂ) * ⟪((1 : R(H0)) : H0 → ℂ), (ξH : H0 → ℂ)⟫ +
            ∑ γ in
                ((Finset.univ.erase
                    (QuotientGroup.lift ε.ker ε (show ε.ker ≤ ε.ker from le_rfl))).filter
                  fun γ => γ.ker = ⊥),
                ⟪((((γ.comp (QuotientGroup.mk' ε.ker)).toCharacterRing - 1 : R(H0)) :
                      H0 → ℂ),
                    (ξH : H0 → ℂ)⟫ =
              algebraMap ℤ ℂ (n * bC))
    (β : (H0 ⧸ M) →* ℂˣ) (hβ : β ≠ 1) :
    ∃ bβ : ℤ,
      ⟪((((β.comp (QuotientGroup.mk' M)).toCharacterRing - 1 : R(H0)) : H0 → ℂ),
          (ξH : H0 → ℂ)⟫ =
        algebraMap ℤ ℂ (n * bβ) := by
  classical
  let ε : H0 →* ℂˣ := β.comp (QuotientGroup.mk' M)
  obtain ⟨hε_ne, hε_ker, hε_lt⟩ :=
    lifted_prime_coatom_character_has_smaller_kernel_index
      δ M hδker_lt_M hprime β hβ
  have hεcyclic :
      ∃ bC : ℤ,
        (ε.ker.index : ℂ) * ⟪((1 : R(H0)) : H0 → ℂ), (ξH : H0 → ℂ)⟫ +
          ∑ γ in
              ((Finset.univ.erase
                  (QuotientGroup.lift ε.ker ε (show ε.ker ≤ ε.ker from le_rfl))).filter
                fun γ => γ.ker = ⊥),
              ⟪((((γ.comp (QuotientGroup.mk' ε.ker)).toCharacterRing - 1 : R(H0)) :
                    H0 → ℂ),
                  (ξH : H0 → ℂ)⟫ =
            algebraMap ℤ ℂ (n * bC) := hm ε hε_ne hε_lt
  -- Convert the smaller-kernel faithful cyclic-layer package for the lift `ε` into the desired
  -- ambient difference witness.
  simpa [ε] using
    difference_divisible_of_kernel_eq_chosen_coatom_of_faithful_cyclic_layer_divisible
      ε hε_ne M ξH hε_ker hprime hMpair hεcyclic

/-- Helper for Remark 11-11.1-3: the quotient by the kernel of a degree-`1` character is cyclic,
because it identifies with the cyclic image of that character. -/
private theorem kernel_quotient_isCyclic_of_nontrivial_character
    {H0 : Type*} [Group H0] [Finite H0]
    (β : H0 →* ℂˣ) (_hβ : β ≠ 1) :
    IsCyclic (H0 ⧸ β.ker) := by
  let e : H0 ⧸ β.ker ≃* β.range := QuotientGroup.quotientKerEquivRange β
  letI : IsCyclic β.range := Representation.degree_one_character_range_isCyclic β
  -- Transport cyclicity across the canonical quotient-range equivalence.
  simpa using e.isCyclic

/-- Helper for Remark 11-11.1-3: the quotient by the kernel of a degree-`1` character is
commutative, because it identifies with a subgroup of `ℂˣ`. -/
private theorem kernel_quotient_mul_comm_of_nontrivial_character
    {H0 : Type*} [Group H0] [Finite H0]
    (β : H0 →* ℂˣ) (_hβ : β ≠ 1) :
    ∀ a b : H0 ⧸ β.ker, a * b = b * a := by
  let e : H0 ⧸ β.ker ≃* β.range := QuotientGroup.quotientKerEquivRange β
  intro a b
  -- Transport commutativity from the range of `β`, which lies in the commutative group `ℂˣ`.
  apply e.injective
  simp [mul_comm]

/-- Helper for Remark 11-11.1-3: the quotient character induced by a nontrivial degree-`1`
character factors through its kernel quotient, stays nontrivial, and lives on a finite cyclic
commutative quotient. -/
private theorem kernel_quotient_distinguished_character_data
    {H0 : Type*} [Group H0] [Finite H0]
    (β : H0 →* ℂˣ) (hβ : β ≠ 1) :
    let βq : (H0 ⧸ β.ker) →* ℂˣ :=
      QuotientGroup.lift β.ker β (show β.ker ≤ β.ker from le_rfl)
    β = βq.comp (QuotientGroup.mk' β.ker) ∧
      βq ≠ 1 ∧
      IsCyclic (H0 ⧸ β.ker) ∧
      (∀ a b : H0 ⧸ β.ker, a * b = b * a) := by
  dsimp
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- The distinguished quotient character is defined precisely by factoring `β` through `mk'`.
    simpa using
      (QuotientGroup.lift_comp_mk' β.ker β (show β.ker ≤ β.ker from le_rfl)).symm
  · -- Nontriviality survives quotienting because precomposing with `mk'` recovers `β`.
    simpa using kernel_quotient_character_ne_one β hβ
  · -- The kernel quotient is cyclic because it identifies with the cyclic image of `β`.
    exact kernel_quotient_isCyclic_of_nontrivial_character β hβ
  · -- The same quotient is commutative because that image lies in `ℂˣ`.
    exact kernel_quotient_mul_comm_of_nontrivial_character β hβ

/-- Helper for Remark 11-11.1-3: after isolating the distinguished quotient character `βq`, the
nonfaithful erased quotient-character summands are exactly the smaller-kernel branch owned by the
induction hypothesis, together with the trivial lifted branch. -/
private theorem nonfaithful_erased_quotient_sum_divisible
    (X : Finset (Subgroup G))
    (hXelem : ∀ H : Subgroup G, H ∈ X ↔ IsElementary H)
    {x : (H : X) → R(H.1)} {t : elementary_coherence_target X hXelem} {n : ℤ}
    (H : X)
    (sH : ((J : (Finset.univ : Finset (Subgroup H.1))) → R(J.1)) →ₗ[ℤ] R(H.1))
    (β : H.1 →* ℂˣ)
    (ih :
      ∀ δ : H.1 →* ℂˣ, δ ≠ 1 → δ.ker.index < β.ker.index →
        let XH : Finset (Subgroup H.1) := Finset.univ
        let ψH : (J : XH) → R(J.1) := fun J ↦
          Subgroup.characterRingTransport
            (J.1.equivMapOfInjective H.1.subtype H.1.subtype_injective)
            (x ⟨J.1.map H.1.subtype,
              (hXelem (J.1.map H.1.subtype)).2 <|
                isElementary_of_mulEquiv_local
                  (J.1.equivMapOfInjective H.1.subtype H.1.subtype_injective)
                  (subgroup_isElementary_of_isElementary_local J.1 ((hXelem H.1).1 H.2))⟩)
        ∃ b : ℤ,
          ⟪((((δ.toCharacterRing - 1 : R(H.1)) : H.1 → ℂ)),
              ((sH ψH : R(H.1)) : H.1 → ℂ)⟫ =
            algebraMap ℤ ℂ (n * b)) :
    let βq : (H.1 ⧸ β.ker) →* ℂˣ :=
      QuotientGroup.lift β.ker β (show β.ker ≤ β.ker from le_rfl)
    let term : ((H.1 ⧸ β.ker) →* ℂˣ) → ℂ := fun γ ↦
      ⟪((((γ.comp (QuotientGroup.mk' β.ker)).toCharacterRing - 1 : R(H.1)) :
            H.1 → ℂ),
          ((sH
              (fun J ↦
                Subgroup.characterRingTransport
                  (J.1.equivMapOfInjective H.1.subtype H.1.subtype_injective)
                  (x ⟨J.1.map H.1.subtype,
                    (hXelem (J.1.map H.1.subtype)).2 <|
                      isElementary_of_mulEquiv_local
                        (J.1.equivMapOfInjective H.1.subtype H.1.subtype_injective)
                        (subgroup_isElementary_of_isElementary_local J.1
                          ((hXelem H.1).1 H.2))⟩)) : R(H.1)) : H.1 → ℂ)⟫
    ∃ bNF : ℤ,
      ∑ γ in ((Finset.univ.erase βq).filter fun γ => γ.ker ≠ ⊥), term γ =
        algebraMap ℤ ℂ (n * bNF) := by
  classical
  dsimp
  suffices hterm :
      ∀ γ ∈ ((Finset.univ.erase βq).filter fun γ => γ.ker ≠ ⊥),
        ∃ bγ : ℤ, term γ = algebraMap ℤ ℂ (n * bγ) by
    obtain ⟨bNF, hbNF⟩ :=
      finset_sum_int_multiples
        (s := (Finset.univ.erase βq).filter fun γ => γ.ker ≠ ⊥)
        (f := term) (n := n) hterm
    refine ⟨bNF, hbNF⟩
  intro γ hγ
  have hγker : γ.ker ≠ ⊥ := by
    simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_univ, true_and] at hγ
    exact hγ.2
  by_cases hδ : γ.comp (QuotientGroup.mk' β.ker) = 1
  · -- The trivial lifted branch contributes the zero difference character.
    simpa [term] using
      erased_quotient_character_difference_divisible_of_comp_eq_one
        X hXelem H sH β γ hδ
  · let δ : H.1 →* ℂˣ := γ.comp (QuotientGroup.mk' β.ker)
    have hδ' : δ ≠ 1 := by
      simpa [δ] using hδ
    have hlt : δ.ker.index < β.ker.index := by
      -- Nonfaithful quotient characters strictly enlarge the ambient kernel.
      simpa [δ] using
        kernel_growth_measure_decreases_on_nonfaithful_erased_branch β γ hγker
    -- The only genuine recursive calls occur in this smaller-kernel branch.
    simpa [term, δ] using ih δ hδ' hlt

/-- Helper for Remark 11-11.1-3: once the cyclic top layer is rewritten into proper overgroups,
each induced trivial summand is already an `n`-multiple by the local proper-branch hypothesis. -/
private theorem proper_induced_trivial_pairing_divisible_of_local_proper_branch
    (X : Finset (Subgroup G))
    (hXelem : ∀ H : Subgroup G, H ∈ X ↔ IsElementary H)
    {x : (H : X) → R(H.1)} {t : elementary_coherence_target X hXelem} {n : ℤ}
    (hdx : elementary_coherence_defect X hXelem x = n • t)
    (H : X)
    (sH : ((J : (Finset.univ : Finset (Subgroup H.1))) → R(J.1)) →ₗ[ℤ] R(H.1))
    (hsH : Function.LeftInverse sH
      (Representation.characterRingRestriction (Finset.univ : Finset (Subgroup H.1))).toLinearMap)
    (hproper :
      ∀ (J : Subgroup H.1) (hJ : J < ⊤) (α : J →* ℂˣ),
        let KX : X := ⟨J.map H.1.subtype,
          (hXelem (J.map H.1.subtype)).2 <|
            isElementary_of_mulEquiv_local
              (J.equivMapOfInjective H.1.subtype H.1.subtype_injective)
              (subgroup_isElementary_of_isElementary_local J ((hXelem H.1).1 H.2))⟩
        ∃ c : ℤ, linear_character_pairing_int H.1 J α (x KX) = n * c)
    (J : Subgroup H.1) (hJ : J < ⊤) :
    let XH : Finset (Subgroup H.1) := Finset.univ
    let ψH : (K : XH) → R(K.1) := fun K ↦
      Subgroup.characterRingTransport
        (K.1.equivMapOfInjective H.1.subtype H.1.subtype_injective)
        (x ⟨K.1.map H.1.subtype,
          (hXelem (K.1.map H.1.subtype)).2 <|
            isElementary_of_mulEquiv_local
              (K.1.equivMapOfInjective H.1.subtype H.1.subtype_injective)
              (subgroup_isElementary_of_isElementary_local K.1 ((hXelem H.1).1 H.2))⟩)
    let ξH : R(H.1) := sH ψH
    ∃ b : ℤ,
      ⟪(Subgroup.characterRingInduction J (1 : R(J)) : H.1 → ℂ), (ξH : H.1 → ℂ)⟫ =
        algebraMap ℤ ℂ (n * b) := by
  classical
  dsimp
  -- This is exactly the proper-branch transport theorem specialized to the trivial character.
  simpa using
    proper_induced_pairing_divisible_of_transport_pairing_int_divisible
      X hXelem hdx H sH hsH J (1 : J →* ℂˣ) (hproper J hJ (1 : J →* ℂˣ))

/-- Helper for Remark 11-11.1-3: multiplying a proper induced-trivial pairing by an integral
coefficient preserves the `n`-divisibility witness coming from the local proper branch. -/
private theorem int_multiple_of_proper_induced_trivial_pairing_divisible_of_local_proper_branch
    (X : Finset (Subgroup G))
    (hXelem : ∀ H : Subgroup G, H ∈ X ↔ IsElementary H)
    {x : (H : X) → R(H.1)} {t : elementary_coherence_target X hXelem} {n : ℤ}
    (hdx : elementary_coherence_defect X hXelem x = n • t)
    (H : X)
    (sH : ((J : (Finset.univ : Finset (Subgroup H.1))) → R(J.1)) →ₗ[ℤ] R(H.1))
    (hsH : Function.LeftInverse sH
      (Representation.characterRingRestriction (Finset.univ : Finset (Subgroup H.1))).toLinearMap)
    (hproper :
      ∀ (J : Subgroup H.1) (hJ : J < ⊤) (α : J →* ℂˣ),
        let KX : X := ⟨J.map H.1.subtype,
          (hXelem (J.map H.1.subtype)).2 <|
            isElementary_of_mulEquiv_local
              (J.equivMapOfInjective H.1.subtype H.1.subtype_injective)
              (subgroup_isElementary_of_isElementary_local J ((hXelem H.1).1 H.2))⟩
        ∃ c : ℤ, linear_character_pairing_int H.1 J α (x KX) = n * c)
    (a : ℤ) (J : Subgroup H.1) (hJ : J < ⊤) :
    let XH : Finset (Subgroup H.1) := Finset.univ
    let ψH : (K : XH) → R(K.1) := fun K ↦
      Subgroup.characterRingTransport
        (K.1.equivMapOfInjective H.1.subtype H.1.subtype_injective)
        (x ⟨K.1.map H.1.subtype,
          (hXelem (K.1.map H.1.subtype)).2 <|
            isElementary_of_mulEquiv_local
              (K.1.equivMapOfInjective H.1.subtype H.1.subtype_injective)
              (subgroup_isElementary_of_isElementary_local K.1 ((hXelem H.1).1 H.2))⟩)
    let ξH : R(H.1) := sH ψH
    ∃ b : ℤ,
      algebraMap ℤ ℂ a *
        ⟪(Subgroup.characterRingInduction J (1 : R(J)) : H.1 → ℂ), (ξH : H.1 → ℂ)⟫ =
          algebraMap ℤ ℂ (n * b) := by
  classical
  dsimp
  obtain ⟨bJ, hbJ⟩ :=
    proper_induced_trivial_pairing_divisible_of_local_proper_branch
      X hXelem hdx H sH hsH hproper J hJ
  refine ⟨a * bJ, ?_⟩
  -- Rescale the already proved proper-branch witness and fold the coefficient back into `ℤ`.
  calc
    algebraMap ℤ ℂ a *
        ⟪(Subgroup.characterRingInduction J (1 : R(J)) : H.1 → ℂ),
            ((sH
                (fun K ↦
                  Subgroup.characterRingTransport
                    (K.1.equivMapOfInjective H.1.subtype H.1.subtype_injective)
                    (x ⟨K.1.map H.1.subtype,
                      (hXelem (K.1.map H.1.subtype)).2 <|
                        isElementary_of_mulEquiv_local
                          (K.1.equivMapOfInjective H.1.subtype H.1.subtype_injective)
                          (subgroup_isElementary_of_isElementary_local K.1
                            ((hXelem H.1).1 H.2))⟩)) : R(H.1)) : H.1 → ℂ)⟫ =
        algebraMap ℤ ℂ a * algebraMap ℤ ℂ (n * bJ) := by
          rw [hbJ]
    _ = algebraMap ℤ ℂ (a * (n * bJ)) := by
          simp [Int.cast_mul]
    _ = algebraMap ℤ ℂ (n * (a * bJ)) := by
          congr 1
          ring

/-- Helper for Remark 11-11.1-3: once the cyclic top layer is expressed as a finite
`ℤ`-combination of proper induced-trivial pairings, the local proper-branch theorem closes the
whole finite sum at once. -/
private theorem interval_overgroup_pairing_sum_divisible_of_local_proper_branch
    (X : Finset (Subgroup G))
    (hXelem : ∀ H : Subgroup G, H ∈ X ↔ IsElementary H)
    {x : (H : X) → R(H.1)} {t : elementary_coherence_target X hXelem} {n : ℤ}
    (hdx : elementary_coherence_defect X hXelem x = n • t)
    (H : X)
    (sH : ((J : (Finset.univ : Finset (Subgroup H.1))) → R(J.1)) →ₗ[ℤ] R(H.1))
    (hsH : Function.LeftInverse sH
      (Representation.characterRingRestriction (Finset.univ : Finset (Subgroup H.1))).toLinearMap)
    (hproper :
      ∀ (J : Subgroup H.1) (hJ : J < ⊤) (α : J →* ℂˣ),
        let KX : X := ⟨J.map H.1.subtype,
          (hXelem (J.map H.1.subtype)).2 <|
            isElementary_of_mulEquiv_local
              (J.equivMapOfInjective H.1.subtype H.1.subtype_injective)
              (subgroup_isElementary_of_isElementary_local J ((hXelem H.1).1 H.2))⟩
        ∃ c : ℤ, linear_character_pairing_int H.1 J α (x KX) = n * c)
    (S : Finset (Subgroup H.1)) (a : Subgroup H.1 → ℤ)
    (hS : ∀ J ∈ S, J < ⊤) :
    let XH : Finset (Subgroup H.1) := Finset.univ
    let ψH : (K : XH) → R(K.1) := fun K ↦
      Subgroup.characterRingTransport
        (K.1.equivMapOfInjective H.1.subtype H.1.subtype_injective)
        (x ⟨K.1.map H.1.subtype,
          (hXelem (K.1.map H.1.subtype)).2 <|
            isElementary_of_mulEquiv_local
              (K.1.equivMapOfInjective H.1.subtype H.1.subtype_injective)
              (subgroup_isElementary_of_isElementary_local K.1 ((hXelem H.1).1 H.2))⟩)
    let ξH : R(H.1) := sH ψH
    ∃ b : ℤ,
      ∑ J in S,
        algebraMap ℤ ℂ (a J) *
          ⟪(Subgroup.characterRingInduction J (1 : R(J)) : H.1 → ℂ), (ξH : H.1 → ℂ)⟫ =
        algebraMap ℤ ℂ (n * b) := by
  classical
  dsimp
  have hterm :
      ∀ J ∈ S,
        ∃ bJ : ℤ,
          algebraMap ℤ ℂ (a J) *
            ⟪(Subgroup.characterRingInduction J (1 : R(J)) : H.1 → ℂ),
                ((sH
                    (fun K ↦
                      Subgroup.characterRingTransport
                        (K.1.equivMapOfInjective H.1.subtype H.1.subtype_injective)
                        (x ⟨K.1.map H.1.subtype,
                          (hXelem (K.1.map H.1.subtype)).2 <|
                            isElementary_of_mulEquiv_local
                              (K.1.equivMapOfInjective H.1.subtype H.1.subtype_injective)
                              (subgroup_isElementary_of_isElementary_local K.1
                                ((hXelem H.1).1 H.2))⟩)) : R(H.1)) : H.1 → ℂ)⟫ =
            algebraMap ℤ ℂ (n * bJ) := by
    intro J hJ
    -- Close each weighted proper-overgroup summand by rescaling the one-term proper-branch
    -- witness.
    simpa using
      int_multiple_of_proper_induced_trivial_pairing_divisible_of_local_proper_branch
        X hXelem hdx H sH hsH hproper (a J) J (hS J hJ)
  obtain ⟨b, hb⟩ :=
    finset_sum_int_multiples
      (s := S)
      (f := fun J ↦
        algebraMap ℤ ℂ (a J) *
          ⟪(Subgroup.characterRingInduction J (1 : R(J)) : H.1 → ℂ),
              ((sH
                  (fun K ↦
                    Subgroup.characterRingTransport
                      (K.1.equivMapOfInjective H.1.subtype H.1.subtype_injective)
                      (x ⟨K.1.map H.1.subtype,
                        (hXelem (K.1.map H.1.subtype)).2 <|
                          isElementary_of_mulEquiv_local
                            (K.1.equivMapOfInjective H.1.subtype H.1.subtype_injective)
                            (subgroup_isElementary_of_isElementary_local K.1
                              ((hXelem H.1).1 H.2))⟩)) : R(H.1)) : H.1 → ℂ)⟫)
      (n := n) hterm
  exact ⟨b, hb⟩

/-- Helper for Remark 11-11.1-3: pulling a proper quotient subgroup back along the quotient map
produces a proper overgroup of the kernel. This isolates the subgroup-transport bookkeeping from
the remaining cyclic pairing rewrite. -/
private theorem quotient_subgroup_comap_above_kernel_and_lt_top
    {H0 : Type*} [Group H0]
    (K : Subgroup H0) (L : Subgroup (H0 ⧸ K)) (hL : L < ⊤) :
    K ≤ Subgroup.comap (QuotientGroup.mk' K) L ∧
      Subgroup.comap (QuotientGroup.mk' K) L < ⊤ := by
  refine ⟨?_, ?_⟩
  · intro x hx
    -- Elements of the kernel map to `1`, and every subgroup contains `1`.
    change QuotientGroup.mk' K x ∈ L
    have hxone : QuotientGroup.mk' K x = 1 := by
      exact (QuotientGroup.eq_one_iff _).2 hx
    simpa [hxone] using L.one_mem
  · refine lt_top_iff_ne_top.mpr ?_
    intro hcomap_top
    apply hL.ne
    -- The quotient map is surjective, so equality after comap forces equality downstairs.
    apply Subgroup.comap_injective (f := QuotientGroup.mk' K) (QuotientGroup.mk'_surjective K)
    simpa [hcomap_top]

/-- Helper for Remark 11-11.1-3: a membership in the span of a ranged family can be repackaged as
an explicit finitely supported `ℤ`-linear combination of that family. -/
private theorem exists_finsupp_eq_sum_of_mem_span_range
    {ι : Type*} {M : Type*} [AddCommGroup M] [Module ℤ M]
    (v : ι → M) {x : M} (hx : x ∈ Submodule.span ℤ (Set.range v)) :
    ∃ c : ι →₀ ℤ, x = c.sum (fun i n ↦ n • v i) := by
  rcases Finsupp.mem_span_range_iff_exists_finsupp.1 hx with ⟨c, hc⟩
  -- Record the span witness as a single finitely supported sum so later subgroup bookkeeping only
  -- has to rearrange one finite support.
  exact ⟨c, hc.symm⟩

/-- Helper for Remark 11-11.1-3: a finitely supported sum indexed by subgroup data can be rewritten
as a finite sum over the ambient subgroup lattice with coefficient function `a`. -/
private theorem subgroup_finsupp_sum_eq_finset_sum
    {H0 : Type*} [Group H0]
    {M : Type*} [AddCommGroup M] [Module ℤ M]
    {P : Subgroup H0 → Prop}
    (v : Subgroup H0 → M)
    (c : {J : Subgroup H0 // P J} →₀ ℤ) :
    ∃ (S : Finset (Subgroup H0)) (a : Subgroup H0 → ℤ),
      (∀ J ∈ S, P J) ∧
        c.sum (fun i n ↦ n • v i.1) = ∑ J in S, a J • v J := by
  classical
  let e : {J : Subgroup H0 // P J} ↪ Subgroup H0 := ⟨Subtype.val, Subtype.val_injective⟩
  let S : Finset (Subgroup H0) := c.support.map e
  have hpre_exists :
      ∀ {J : Subgroup H0}, J ∈ S → ∃ i : {J : Subgroup H0 // P J}, i ∈ c.support ∧ i.1 = J := by
    intro J hJ
    rcases Finset.mem_map.1 hJ with ⟨i, hi, hiJ⟩
    exact ⟨i, hi, hiJ⟩
  let preimageOfMem : ∀ J : Subgroup H0, J ∈ S → {J : Subgroup H0 // P J} :=
    fun J hJ ↦ Classical.choose (hpre_exists hJ)
  have hpre_mem :
      ∀ {J : Subgroup H0} (hJ : J ∈ S), preimageOfMem J hJ ∈ c.support := by
    intro J hJ
    exact (Classical.choose_spec (hpre_exists hJ)).1
  have hpre_val :
      ∀ {J : Subgroup H0} (hJ : J ∈ S), (preimageOfMem J hJ).1 = J := by
    intro J hJ
    exact (Classical.choose_spec (hpre_exists hJ)).2
  let a : Subgroup H0 → ℤ := fun J ↦ if hJ : J ∈ S then c (preimageOfMem J hJ) else 0
  refine ⟨S, a, ?_, ?_⟩
  · intro J hJ
    -- Membership in the mapped support remembers the original subgroup proof `P J`.
    exact (preimageOfMem J hJ).2
  · have hsum :
        ∑ J in S, a J • v J = ∑ i in c.support, c i • v i.1 := by
      refine Finset.sum_bij (fun J hJ ↦ preimageOfMem J hJ) ?_ ?_ ?_ ?_
      · intro J hJ
        exact hpre_mem hJ
      · intro J hJ
        -- The chosen preimage has the same ambient subgroup, so the summand only changes notation.
        simp [a, hJ, hpre_val hJ]
      · intro J₁ J₂ hJ₁ hJ₂ hEq
        exact Subtype.ext (congrArg Subtype.val hEq)
      · intro i hi
        refine ⟨i.1, Finset.mem_map.2 ⟨i, hi, rfl⟩, ?_⟩
        -- The support map is injective, so the chosen preimage of `i.1` is exactly `i`.
        apply Subtype.ext
        simpa using hpre_val (J := i.1) (Finset.mem_map.2 ⟨i, hi, rfl⟩)
    -- Replace the finitely supported sum by the ambient subgroup-indexed finite sum.
    calc
      c.sum (fun i n ↦ n • v i.1) = ∑ i in c.support, c i • v i.1 := by
        simp [Finsupp.sum]
      _ = ∑ J in S, a J • v J := hsum.symm

/-- Helper for Remark 11-11.1-3: once the cyclic top-layer scalar is known to lie in the span of
the paired induced-trivial contributions from proper overgroups of the kernel, it can be packaged
in the exact finite interval form used by the pairing theorem. -/
private theorem exists_overgroup_finset_sum_of_mem_span_pairings
    {H0 : Type*} [Group H0] [Finite H0]
    (β : H0 →* ℂˣ) (ξ : R(H0)) {z : ℂ}
    (hz :
      z ∈ Submodule.span ℤ
        (Set.range fun J : {J : Subgroup H0 // β.ker ≤ J ∧ J < ⊤} ↦
          ⟪(Subgroup.characterRingInduction J.1 (1 : R(J.1)) : H0 → ℂ), (ξ : H0 → ℂ)⟫)) :
    ∃ (S : Finset (Subgroup H0)) (a : Subgroup H0 → ℤ),
      (∀ J ∈ S, β.ker ≤ J ∧ J < ⊤) ∧
        z = ∑ J in S,
          algebraMap ℤ ℂ (a J) *
            ⟪(Subgroup.characterRingInduction J (1 : R(J)) : H0 → ℂ), (ξ : H0 → ℂ)⟫ := by
  obtain ⟨c, hc⟩ :=
    exists_finsupp_eq_sum_of_mem_span_range
      (v := fun J : {J : Subgroup H0 // β.ker ≤ J ∧ J < ⊤} ↦
        ⟪(Subgroup.characterRingInduction J.1 (1 : R(J.1)) : H0 → ℂ), (ξ : H0 → ℂ)⟫) hz
  obtain ⟨S, a, hS, ha⟩ :=
    subgroup_finsupp_sum_eq_finset_sum
      (v := fun J : Subgroup H0 ↦
        (⟪(Subgroup.characterRingInduction J (1 : R(J)) : H0 → ℂ), (ξ : H0 → ℂ)⟫ : ℂ)) c
  refine ⟨S, a, hS, ?_⟩
  -- The new helpers separate the unresolved scalar span membership from the routine finite-support
  -- packaging demanded by the target theorem.
  calc
    z =
        c.sum
          (fun i n ↦ n • ⟪(Subgroup.characterRingInduction i.1 (1 : R(i.1)) : H0 → ℂ),
            (ξ : H0 → ℂ)⟫) := hc
    _ =
        ∑ J in S,
          a J • (⟪(Subgroup.characterRingInduction J (1 : R(J)) : H0 → ℂ),
            (ξ : H0 → ℂ)⟫ : ℂ) := ha
    _ =
        ∑ J in S,
          algebraMap ℤ ℂ (a J) *
            ⟪(Subgroup.characterRingInduction J (1 : R(J)) : H0 → ℂ), (ξ : H0 → ℂ)⟫ := by
          refine Finset.sum_congr rfl ?_
          intro J hJ
          simp [zsmul_eq_mul]

/-- Helper for Remark 11-11.1-3: transporting a proper quotient subgroup `L < ⊤` of
`H.1 ⧸ β.ker` back along the quotient map produces a proper overgroup of `β.ker`, so the
ambient proper-branch divisibility theorem applies directly to its induced trivial pairing. -/
private theorem proper_quotient_induced_trivial_pairing_divisible_of_local_proper_branch
    (X : Finset (Subgroup G))
    (hXelem : ∀ H : Subgroup G, H ∈ X ↔ IsElementary H)
    {x : (H : X) → R(H.1)} {t : elementary_coherence_target X hXelem} {n : ℤ}
    (hdx : elementary_coherence_defect X hXelem x = n • t)
    (H : X)
    (sH : ((J : (Finset.univ : Finset (Subgroup H.1))) → R(J.1)) →ₗ[ℤ] R(H.1))
    (hsH : Function.LeftInverse sH
      (Representation.characterRingRestriction (Finset.univ : Finset (Subgroup H.1))).toLinearMap)
    (hproper :
      ∀ (J : Subgroup H.1) (hJ : J < ⊤) (α : J →* ℂˣ),
        let KX : X := ⟨J.map H.1.subtype,
          (hXelem (J.map H.1.subtype)).2 <|
            isElementary_of_mulEquiv_local
              (J.equivMapOfInjective H.1.subtype H.1.subtype_injective)
              (subgroup_isElementary_of_isElementary_local J ((hXelem H.1).1 H.2))⟩
        ∃ c : ℤ, linear_character_pairing_int H.1 J α (x KX) = n * c)
    (β : H.1 →* ℂˣ)
    (L : Subgroup (H.1 ⧸ β.ker)) (hL : L < ⊤) :
    let XH : Finset (Subgroup H.1) := Finset.univ
    let ψH : (J : XH) → R(J.1) := fun J ↦
      Subgroup.characterRingTransport
        (J.1.equivMapOfInjective H.1.subtype H.1.subtype_injective)
        (x ⟨J.1.map H.1.subtype,
          (hXelem (J.1.map H.1.subtype)).2 <|
            isElementary_of_mulEquiv_local
              (J.1.equivMapOfInjective H.1.subtype H.1.subtype_injective)
              (subgroup_isElementary_of_isElementary_local J.1 ((hXelem H.1).1 H.2))⟩)
    let ξH : R(H.1) := sH ψH
    let J : Subgroup H.1 := Subgroup.comap (QuotientGroup.mk' β.ker) L
    ∃ bL : ℤ,
      ⟪(Subgroup.characterRingInduction J (1 : R(J)) : H.1 → ℂ), (ξH : H.1 → ℂ)⟫ =
        algebraMap ℤ ℂ (n * bL) := by
  classical
  dsimp
  obtain ⟨_, hJlt⟩ :=
    quotient_subgroup_comap_above_kernel_and_lt_top β.ker L hL
  -- The quotient subgroup bookkeeping is now finished: the pullback subgroup is proper in `H.1`,
  -- so the previously established proper-branch arithmetic closes the pairing.
  simpa using
    proper_induced_trivial_pairing_divisible_of_local_proper_branch
      X hXelem hdx H sH hsH hproper (Subgroup.comap (QuotientGroup.mk' β.ker) L) hJlt

/-- Helper for Remark 11-11.1-3: pull a quotient-side character-ring element back along the
kernel quotient and pair it against the fixed ambient test character. -/
private noncomputable def quotient_pullback_pairing_linearMap
    {H0 : Type*} [Group H0] [Finite H0]
    (β : H0 →* ℂˣ) (ξ : R(H0)) :
    R(H0 ⧸ β.ker) →ₗ[ℤ] ℂ :=
  { toFun := fun η ↦
      ⟪(fun x : H0 ↦ ((η : H0 ⧸ β.ker → ℂ) (QuotientGroup.mk' β.ker x))), (ξ : H0 → ℂ)⟫
    map_add' := by
      intro η θ
      -- The pullback pairing is additive because the pairing is additive in its left slot.
      simp [Representation.groupFunctionPairing_add_left]
    map_smul' := by
      intro a η
      -- The same pullback pairing is `ℤ`-linear in its left slot.
      simpa [zsmul_eq_mul] using
        (Representation.groupFunctionPairing_smul_left
          (a := (a : ℂ))
          (φ := fun x : H0 ↦ ((η : H0 ⧸ β.ker → ℂ) (QuotientGroup.mk' β.ker x)))
          (ψ := (ξ : H0 → ℂ))) }

/-- Helper for Remark 11-11.1-3: the quotient pullback pairing sends the quotient trivial
character to the ambient trivial-line pairing. -/
private theorem quotient_pullback_pairing_linearMap_one
    {H0 : Type*} [Group H0] [Finite H0]
    (β : H0 →* ℂˣ) (ξ : R(H0)) :
    quotient_pullback_pairing_linearMap β ξ (1 : R(H0 ⧸ β.ker)) =
      ⟪((1 : R(H0)) : H0 → ℂ), (ξ : H0 → ℂ)⟫ := by
  -- Pulling back the quotient unit character along `mk'` leaves the constant-one function.
  simp [quotient_pullback_pairing_linearMap]

/-- Helper for Remark 11-11.1-3: evaluating the quotient pullback pairing on a quotient
linear-character difference gives exactly the ambient erased-difference term. -/
private theorem quotient_pullback_pairing_linearMap_difference
    {H0 : Type*} [Group H0] [Finite H0]
    (β : H0 →* ℂˣ) (ξ : R(H0))
    (γ : (H0 ⧸ β.ker) →* ℂˣ) :
    quotient_pullback_pairing_linearMap β ξ (γ.toCharacterRing - 1) =
      ⟪((((γ.comp (QuotientGroup.mk' β.ker)).toCharacterRing - 1 : R(H0)) : H0 → ℂ),
          (ξ : H0 → ℂ)⟫ := by
  -- Expanding the pullback definition turns the quotient-side generator into the ambient erased
  -- quotient-character difference term used throughout the kernel recursion.
  simp [quotient_pullback_pairing_linearMap, MonoidHom.toCharacterRing_apply]

/-- Helper for Remark 11-11.1-3: pulling the quotient induced trivial character back along the
kernel quotient agrees pointwise with induction from the comap subgroup upstairs. -/
private theorem quotient_induced_trivial_pullback_eq_comap_induction
    {H0 : Type*} [Group H0] [Finite H0]
    (β : H0 →* ℂˣ)
    (L : Subgroup (H0 ⧸ β.ker)) :
    (fun x : H0 ↦
        ((Subgroup.characterRingInduction L (1 : R(L)) : R(H0 ⧸ β.ker)) :
          H0 ⧸ β.ker → ℂ) (QuotientGroup.mk' β.ker x)) =
      (Subgroup.characterRingInduction
          (Subgroup.comap (QuotientGroup.mk' β.ker) L)
          (1 : R(Subgroup.comap (QuotientGroup.mk' β.ker) L)) : H0 → ℂ) := by
  classical
  let e : H0 ⧸ β.ker ≃* β.range := QuotientGroup.quotientKerEquivRange β
  letI : CommGroup (H0 ⧸ β.ker) :=
    { QuotientGroup.Quotient.group β.ker with
      mul_comm := by
        intro a b
        apply e.injective
        simp [mul_comm] }
  let J : Subgroup H0 := Subgroup.comap (QuotientGroup.mk' β.ker) L
  have hindex : (J.index : ℂ) = (L.index : ℂ) := by
    have hcard :
        Fintype.card (H0 ⧸ J) = Fintype.card ((H0 ⧸ β.ker) ⧸ L) := by
      exact
        Fintype.card_congr
          (QuotientMonomialReduction.quotient_comap_leftCosetEquiv_local
            (Q := H0) (N := β.ker) L)
    -- The quotient-coset equivalence identifies the two subgroup indices.
    simpa [J, Subgroup.index_eq_card] using congrArg (fun n : ℕ ↦ (n : ℂ)) hcard
  ext x
  have hmk :
      QuotientGroup.mk' L (QuotientGroup.mk' β.ker x) = 1 ↔ QuotientGroup.mk' J x = 1 := by
    constructor
    · intro hx
      apply (Subgroup.quotient_mk'_eq_one_iff J x).2
      -- Triviality downstairs is exactly membership in the comap subgroup upstairs.
      change QuotientGroup.mk' β.ker x ∈ L
      exact (Subgroup.quotient_mk'_eq_one_iff L (QuotientGroup.mk' β.ker x)).1 hx
    · intro hx
      apply (Subgroup.quotient_mk'_eq_one_iff L (QuotientGroup.mk' β.ker x)).2
      -- Conversely, membership in the comap subgroup is the defining pullback condition.
      change x ∈ J at hx
      simpa [J] using hx
  rw [Subgroup.characterRingInduction_apply, Subgroup.characterRingInduction_apply]
  rw [Subgroup.induced_trivial_apply_eq_ite_index_zero (H := L)
      (g := QuotientGroup.mk' β.ker x)]
  rw [Subgroup.induced_trivial_apply_eq_ite_index_zero (H := J) (g := x)]
  by_cases hx : QuotientGroup.mk' J x = 1
  · have hxL : QuotientGroup.mk' L (QuotientGroup.mk' β.ker x) = 1 := (hmk).2 hx
    -- In the fixed-point case, both induced trivial characters take the common index value.
    simp [hx, hxL, hindex]
  · have hxL : QuotientGroup.mk' L (QuotientGroup.mk' β.ker x) ≠ 1 := by
      intro hxL
      exact hx ((hmk).1 hxL)
    -- Away from the pulled-back subgroup, both induced trivial characters vanish.
    simp [hx, hxL]

/-- Helper for Remark 11-11.1-3: pulling the quotient induced trivial character back along the
kernel quotient identifies it with induction from the comap subgroup upstairs. -/
private theorem quotient_pullback_pairing_linearMap_induced_trivial
    {H0 : Type*} [Group H0] [Finite H0]
    (β : H0 →* ℂˣ) (ξ : R(H0))
    (L : Subgroup (H0 ⧸ β.ker)) :
    quotient_pullback_pairing_linearMap β ξ (Subgroup.characterRingInduction L (1 : R(L))) =
      ⟪(Subgroup.characterRingInduction
            (Subgroup.comap (QuotientGroup.mk' β.ker) L)
            (1 : R(Subgroup.comap (QuotientGroup.mk' β.ker) L)) : H0 → ℂ),
          (ξ : H0 → ℂ)⟫ := by
  -- Apply the pairing functional to the pointwise pullback/comap identification proved above.
  simpa [quotient_pullback_pairing_linearMap] using
    congrArg
      (fun φ : H0 → ℂ ↦ ⟪φ, (ξ : H0 → ℂ)⟫)
      (quotient_induced_trivial_pullback_eq_comap_induction β L)

/-- Helper for Remark 11-11.1-3: a span relation among quotient pullback pairings over proper
quotient subgroups can be repackaged as an explicit finite `ℤ`-linear combination. -/
private theorem quotient_pairing_span_to_finset_sum
    {H0 : Type*} [Group H0] [Finite H0]
    (β : H0 →* ℂˣ) (ξ : R(H0)) {z : ℂ}
    (hz :
      z ∈ Submodule.span ℤ
        (Set.range fun L : {L : Subgroup (H0 ⧸ β.ker) // L < ⊤} ↦
          quotient_pullback_pairing_linearMap β ξ
            (Subgroup.characterRingInduction L.1 (1 : R(L.1))))) :
    ∃ S : Finset (Subgroup (H0 ⧸ β.ker)), ∃ a : Subgroup (H0 ⧸ β.ker) → ℤ,
      (∀ L ∈ S, L < ⊤) ∧
      z = ∑ L in S,
        algebraMap ℤ ℂ (a L) *
          quotient_pullback_pairing_linearMap β ξ
            (Subgroup.characterRingInduction L (1 : R(L))) := by
  obtain ⟨c, hc⟩ :=
    exists_finsupp_eq_sum_of_mem_span_range
      (v := fun L : {L : Subgroup (H0 ⧸ β.ker) // L < ⊤} ↦
        quotient_pullback_pairing_linearMap β ξ
          (Subgroup.characterRingInduction L.1 (1 : R(L.1)))) hz
  obtain ⟨S, a, hS, ha⟩ :=
    subgroup_finsupp_sum_eq_finset_sum
      (v := fun L : Subgroup (H0 ⧸ β.ker) ↦
        (quotient_pullback_pairing_linearMap β ξ
          (Subgroup.characterRingInduction L (1 : R(L))) : ℂ)) c
  refine ⟨S, a, hS, ?_⟩
  -- Repackage the finitely supported span witness as the concrete finite sum needed later.
  calc
    z =
        c.sum
          (fun i n ↦ n •
            quotient_pullback_pairing_linearMap β ξ
              (Subgroup.characterRingInduction i.1 (1 : R(i.1)))) := hc
    _ =
        ∑ L in S,
          a L •
            (quotient_pullback_pairing_linearMap β ξ
              (Subgroup.characterRingInduction L (1 : R(L))) : ℂ) := ha
    _ =
        ∑ L in S,
          algebraMap ℤ ℂ (a L) *
            quotient_pullback_pairing_linearMap β ξ
              (Subgroup.characterRingInduction L (1 : R(L))) := by
          refine Finset.sum_congr rfl ?_
          intro L hL
          simp [zsmul_eq_mul]

/-- Helper for Remark 11-11.1-3: applying the quotient pullback pairing to the Chapter 10 cyclic
quotient identity rewrites an induced trivial quotient character as the index-scaled trivial line
plus the full quotient-character difference family. -/
private theorem quotient_pullback_pairing_induced_trivial_eq_index_trivial_add_difference_sum
    {H0 : Type*} [Group H0] [Finite H0]
    (β : H0 →* ℂˣ) (ξ : R(H0))
    (M : Subgroup (H0 ⧸ β.ker)) [M.Normal]
    (hcomm : ∀ a b : (H0 ⧸ β.ker) ⧸ M, a * b = b * a)
    [Fintype (((H0 ⧸ β.ker) ⧸ M) →* ℂˣ)] :
    quotient_pullback_pairing_linearMap β ξ
      (Subgroup.characterRingInduction M (1 : R(M))) =
      (M.index : ℂ) * quotient_pullback_pairing_linearMap β ξ (1 : R(H0 ⧸ β.ker)) +
        ∑ δ : ((H0 ⧸ β.ker) ⧸ M) →* ℂˣ,
          quotient_pullback_pairing_linearMap β ξ
            (((δ.comp (QuotientGroup.mk' M)).toCharacterRing - 1 : R(H0 ⧸ β.ker))) := by
  have hrewrite :
      quotient_pullback_pairing_linearMap β ξ
        (Subgroup.characterRingInduction M (1 : R(M))) -
          (M.index : ℂ) * quotient_pullback_pairing_linearMap β ξ (1 : R(H0 ⧸ β.ker)) =
        ∑ δ : ((H0 ⧸ β.ker) ⧸ M) →* ℂˣ,
          quotient_pullback_pairing_linearMap β ξ
            (((δ.comp (QuotientGroup.mk' M)).toCharacterRing - 1 : R(H0 ⧸ β.ker))) := by
    -- Apply the quotient pullback linear functional directly to the quotient-character identity.
    simpa [LinearMap.map_sub, LinearMap.map_zsmul, zsmul_eq_mul] using
      congrArg
        (quotient_pullback_pairing_linearMap β ξ)
        (induced_trivial_sub_index_smul_one_eq_sum_quotient_linearCharacter_differences
          (G := H0 ⧸ β.ker) (H := M) hcomm)
  -- Move the scaled trivial-line term to the right so later arguments can split the quotient
  -- character family by kernel type.
  exact (sub_eq_iff_eq_add.1 hrewrite).trans <| by
    simp [add_comm, add_left_comm, add_assoc]

/-- Helper for Remark 11-11.1-3: after isolating a nontrivial quotient character on the kernel
quotient, the quotient pullback pairing sees its kernel-induced trivial character as the
index-scaled trivial line, the distinguished difference term, and the remaining erased branch. -/
private theorem quotient_pullback_pairing_kernel_induced_decomposes_with_distinguished_difference
    {H0 : Type*} [Group H0] [Finite H0]
    (β : H0 →* ℂˣ) (ξ : R(H0))
    (γ : (H0 ⧸ β.ker) →* ℂˣ) (hγ : γ ≠ 1) :
    let γq : ((H0 ⧸ β.ker) ⧸ γ.ker) →* ℂˣ :=
      QuotientGroup.lift γ.ker γ (show γ.ker ≤ γ.ker from le_rfl)
    quotient_pullback_pairing_linearMap β ξ
      (Subgroup.characterRingInduction γ.ker (1 : R(γ.ker))) =
      (γ.ker.index : ℂ) * quotient_pullback_pairing_linearMap β ξ (1 : R(H0 ⧸ β.ker)) +
        quotient_pullback_pairing_linearMap β ξ (γ.toCharacterRing - 1) +
          ∑ δ in Finset.univ.erase γq,
            quotient_pullback_pairing_linearMap β ξ
              (((δ.comp (QuotientGroup.mk' γ.ker)).toCharacterRing - 1 :
                  R((H0 ⧸ β.ker)))) := by
  classical
  dsimp
  obtain ⟨hγ_factor, hγq_ne, _, hcomm⟩ :=
    kernel_quotient_distinguished_character_data (H0 := H0 ⧸ β.ker) γ hγ
  letI : CommGroup (((H0 ⧸ β.ker) ⧸ γ.ker)) :=
    { QuotientGroup.Quotient.group γ.ker with
      mul_comm := hcomm }
  letI : Fintype ((((H0 ⧸ β.ker) ⧸ γ.ker) →* ℂˣ)) := linearCharacterFintype
  let γq : ((H0 ⧸ β.ker) ⧸ γ.ker) →* ℂˣ :=
    QuotientGroup.lift γ.ker γ (show γ.ker ≤ γ.ker from le_rfl)
  let term : (((H0 ⧸ β.ker) ⧸ γ.ker) →* ℂˣ) → ℂ := fun δ ↦
    quotient_pullback_pairing_linearMap β ξ
      (((δ.comp (QuotientGroup.mk' γ.ker)).toCharacterRing - 1 : R((H0 ⧸ β.ker))))
  have hsplit :
      ∑ δ : ((H0 ⧸ β.ker) ⧸ γ.ker) →* ℂˣ, term δ =
        term γq + ∑ δ in Finset.univ.erase γq, term δ := by
    -- Isolate the distinguished quotient character from the full quotient-character family.
    simpa [term] using
      (Finset.sum_erase_add (s := Finset.univ) (a := γq) (by simp)).symm
  have hγq_term :
      term γq =
        quotient_pullback_pairing_linearMap β ξ (γ.toCharacterRing - 1) := by
    -- The distinguished quotient character recovers `γ` after precomposing with the quotient map.
    simpa [term, γq, hγ_factor]
  -- Apply the previous quotient-side identity and then split off the distinguished quotient
  -- character from the remaining family.
  calc
    quotient_pullback_pairing_linearMap β ξ
        (Subgroup.characterRingInduction γ.ker (1 : R(γ.ker))) =
      (γ.ker.index : ℂ) * quotient_pullback_pairing_linearMap β ξ (1 : R(H0 ⧸ β.ker)) +
        ∑ δ : ((H0 ⧸ β.ker) ⧸ γ.ker) →* ℂˣ, term δ := by
          simpa [term] using
            quotient_pullback_pairing_induced_trivial_eq_index_trivial_add_difference_sum
              (β := β) (ξ := ξ) (M := γ.ker) hcomm
    _ =
      (γ.ker.index : ℂ) * quotient_pullback_pairing_linearMap β ξ (1 : R(H0 ⧸ β.ker)) +
        (term γq + ∑ δ in Finset.univ.erase γq, term δ) := by
          rw [hsplit]
    _ =
      (γ.ker.index : ℂ) * quotient_pullback_pairing_linearMap β ξ (1 : R(H0 ⧸ β.ker)) +
        quotient_pullback_pairing_linearMap β ξ (γ.toCharacterRing - 1) +
          ∑ δ in Finset.univ.erase γq, term δ := by
            simpa [hγq_term, add_assoc]

/-- Helper for Remark 11-11.1-3: the cyclic quotient top layer belongs to the `ℤ`-span generated
by the induced trivial pairings coming from proper overgroups of the kernel. This is the exact
source-faithful bridge needed before packaging the top layer as a finite overgroup sum. -/
private theorem faithful_quotient_top_layer_eq_quotient_pullback_pairing
    {H0 : Type*} [Group H0] [Finite H0]
    (β : H0 →* ℂˣ) (ξ : R(H0)) :
    let βq : (H0 ⧸ β.ker) →* ℂˣ :=
      QuotientGroup.lift β.ker β (show β.ker ≤ β.ker from le_rfl)
    let term : ((H0 ⧸ β.ker) →* ℂˣ) → ℂ := fun γ ↦
      ⟪((((γ.comp (QuotientGroup.mk' β.ker)).toCharacterRing - 1 : R(H0)) :
            H0 → ℂ),
          (ξ : H0 → ℂ)⟫
    let η : R(H0 ⧸ β.ker) :=
      (β.ker.index : ℤ) • (1 : R(H0 ⧸ β.ker)) +
        ∑ γ in ((Finset.univ.erase βq).filter fun γ => γ.ker = ⊥),
          ((γ.toCharacterRing - 1 : R(H0 ⧸ β.ker)))
    (β.ker.index : ℂ) * ⟪((1 : R(H0)) : H0 → ℂ), (ξ : H0 → ℂ)⟫ +
        ∑ γ in ((Finset.univ.erase βq).filter fun γ => γ.ker = ⊥), term γ =
      quotient_pullback_pairing_linearMap β ξ η := by
  classical
  dsimp
  let βq : (H0 ⧸ β.ker) →* ℂˣ :=
    QuotientGroup.lift β.ker β (show β.ker ≤ β.ker from le_rfl)
  let term : ((H0 ⧸ β.ker) →* ℂˣ) → ℂ := fun γ ↦
    ⟪((((γ.comp (QuotientGroup.mk' β.ker)).toCharacterRing - 1 : R(H0)) :
          H0 → ℂ),
        (ξ : H0 → ℂ)⟫
  have hone :
      quotient_pullback_pairing_linearMap β ξ ((β.ker.index : ℤ) • (1 : R(H0 ⧸ β.ker))) =
        (β.ker.index : ℂ) * ⟪((1 : R(H0)) : H0 → ℂ), (ξ : H0 → ℂ)⟫ := by
    -- Rewrite the index-scaled quotient trivial character by linearity and then pull it back.
    calc
      quotient_pullback_pairing_linearMap β ξ ((β.ker.index : ℤ) • (1 : R(H0 ⧸ β.ker))) =
          (β.ker.index : ℤ) • quotient_pullback_pairing_linearMap β ξ (1 : R(H0 ⧸ β.ker)) := by
            simp
      _ = (β.ker.index : ℤ) • ⟪((1 : R(H0)) : H0 → ℂ), (ξ : H0 → ℂ)⟫ := by
            rw [quotient_pullback_pairing_linearMap_one]
      _ = (β.ker.index : ℂ) * ⟪((1 : R(H0)) : H0 → ℂ), (ξ : H0 → ℂ)⟫ := by
            simp [zsmul_eq_mul]
  have hsum :
      quotient_pullback_pairing_linearMap β ξ
          (∑ γ in ((Finset.univ.erase βq).filter fun γ => γ.ker = ⊥),
            ((γ.toCharacterRing - 1 : R(H0 ⧸ β.ker)))) =
        ∑ γ in ((Finset.univ.erase βq).filter fun γ => γ.ker = ⊥), term γ := by
    -- Each faithful erased quotient-character difference pulls back to the ambient erased term.
    simp [term, quotient_pullback_pairing_linearMap_difference]
  -- The whole top layer is the pullback pairing applied to the quotient-side faithful package.
  calc
    (β.ker.index : ℂ) * ⟪((1 : R(H0)) : H0 → ℂ), (ξ : H0 → ℂ)⟫ +
        ∑ γ in ((Finset.univ.erase βq).filter fun γ => γ.ker = ⊥), term γ =
      quotient_pullback_pairing_linearMap β ξ ((β.ker.index : ℤ) • (1 : R(H0 ⧸ β.ker))) +
        quotient_pullback_pairing_linearMap β ξ
          (∑ γ in ((Finset.univ.erase βq).filter fun γ => γ.ker = ⊥),
            ((γ.toCharacterRing - 1 : R(H0 ⧸ β.ker)))) := by
              rw [← hone, ← hsum]
    _ =
      quotient_pullback_pairing_linearMap β ξ
        ((β.ker.index : ℤ) • (1 : R(H0 ⧸ β.ker)) +
          ∑ γ in ((Finset.univ.erase βq).filter fun γ => γ.ker = ⊥),
            ((γ.toCharacterRing - 1 : R(H0 ⧸ β.ker)))) := by
              simp

/-- Helper for Remark 11-11.1-3: once the quotient-side faithful top layer itself has pairing
divisible by `n`, the displayed faithful cyclic-layer scalar on the ambient group has the same
divisibility. -/
private theorem faithful_quotient_top_layer_divisible_of_pullback_divisible
    {H0 : Type*} [Group H0] [Finite H0] {n : ℤ}
    (β : H0 →* ℂˣ) (ξ : R(H0))
    (hdiv :
      let βq : (H0 ⧸ β.ker) →* ℂˣ :=
        QuotientGroup.lift β.ker β (show β.ker ≤ β.ker from le_rfl)
      let η : R(H0 ⧸ β.ker) :=
        (β.ker.index : ℤ) • (1 : R(H0 ⧸ β.ker)) +
          ∑ γ in ((Finset.univ.erase βq).filter fun γ => γ.ker = ⊥),
            ((γ.toCharacterRing - 1 : R(H0 ⧸ β.ker)))
      ∃ b : ℤ, quotient_pullback_pairing_linearMap β ξ η = algebraMap ℤ ℂ (n * b)) :
    ∃ b : ℤ,
      (β.ker.index : ℂ) * ⟪((1 : R(H0)) : H0 → ℂ), (ξ : H0 → ℂ)⟫ +
        ∑ γ in ((Finset.univ.erase
            (QuotientGroup.lift β.ker β (show β.ker ≤ β.ker from le_rfl))).filter
          fun γ => γ.ker = ⊥),
          ⟪((((γ.comp (QuotientGroup.mk' β.ker)).toCharacterRing - 1 : R(H0)) :
                H0 → ℂ),
              (ξ : H0 → ℂ)⟫ =
        algebraMap ℤ ℂ (n * b) := by
  classical
  dsimp at hdiv ⊢
  rcases hdiv with ⟨b, hb⟩
  refine ⟨b, ?_⟩
  -- Rewrite the ambient faithful layer back to the quotient-pullback pairing, then use the
  -- packaged quotient-side divisibility witness unchanged.
  calc
    (β.ker.index : ℂ) * ⟪((1 : R(H0)) : H0 → ℂ), (ξ : H0 → ℂ)⟫ +
        ∑ γ in ((Finset.univ.erase
            (QuotientGroup.lift β.ker β (show β.ker ≤ β.ker from le_rfl))).filter
          fun γ => γ.ker = ⊥),
          ⟪((((γ.comp (QuotientGroup.mk' β.ker)).toCharacterRing - 1 : R(H0)) :
                H0 → ℂ),
              (ξ : H0 → ℂ)⟫ =
      quotient_pullback_pairing_linearMap β ξ
        ((β.ker.index : ℤ) • (1 : R(H0 ⧸ β.ker)) +
          ∑ γ in ((Finset.univ.erase
              (QuotientGroup.lift β.ker β (show β.ker ≤ β.ker from le_rfl))).filter
            fun γ => γ.ker = ⊥),
            ((γ.toCharacterRing - 1 : R(H0 ⧸ β.ker)))) := by
          simpa using faithful_quotient_top_layer_eq_quotient_pullback_pairing (β := β) (ξ := ξ)
    _ = algebraMap ℤ ℂ (n * b) := hb

/-- Helper for Remark 11-11.1-3: once the faithful quotient block is known to lie in the
`ℤ`-span of proper quotient induced-trivial characters, applying the quotient pullback pairing
transports that span directly to the ambient overgroup pairing span. -/
private theorem quotient_pullback_pairing_mem_span_overgroups_of_mem_span_induced_trivial
    {H0 : Type*} [Group H0] [Finite H0]
    (β : H0 →* ℂˣ) (ξ : R(H0)) {η : R(H0 ⧸ β.ker)}
    (hη :
      η ∈ Submodule.span ℤ
        (Set.range fun L : {L : Subgroup (H0 ⧸ β.ker) // L < ⊤} ↦
          Subgroup.characterRingInduction L.1 (1 : R(L.1)))) :
    quotient_pullback_pairing_linearMap β ξ η ∈
      Submodule.span ℤ
        (Set.range fun J : {J : Subgroup H0 // β.ker ≤ J ∧ J < ⊤} ↦
          ⟪(Subgroup.characterRingInduction J.1 (1 : R(J.1)) : H0 → ℂ), (ξ : H0 → ℂ)⟫) := by
  -- Push the quotient-side span statement through the pairing linear map one generator at a time.
  refine Submodule.span_induction hη ?_ ?_ ?_ ?_
  · intro ζ hζ
    rcases hζ with ⟨L, rfl⟩
    obtain ⟨hKer, hLtTop⟩ :=
      quotient_subgroup_comap_above_kernel_and_lt_top β.ker L.1 L.2
    have hgen :
        ⟪(Subgroup.characterRingInduction
              (Subgroup.comap (QuotientGroup.mk' β.ker) L.1)
              (1 : R(Subgroup.comap (QuotientGroup.mk' β.ker) L.1)) : H0 → ℂ),
            (ξ : H0 → ℂ)⟫ ∈
          Submodule.span ℤ
            (Set.range fun J : {J : Subgroup H0 // β.ker ≤ J ∧ J < ⊤} ↦
              ⟪(Subgroup.characterRingInduction J.1 (1 : R(J.1)) : H0 → ℂ), (ξ : H0 → ℂ)⟫) := by
      -- The comap subgroup is exactly one ambient proper overgroup generator.
      refine Submodule.subset_span ?_
      refine ⟨⟨Subgroup.comap (QuotientGroup.mk' β.ker) L.1, hKer, hLtTop⟩, ?_⟩
      simp
    -- Rewrite the quotient-side generator by the pullback/comap identification.
    simpa [quotient_pullback_pairing_linearMap_induced_trivial] using hgen
  · -- The zero vector maps to zero, which is always in the target span.
    simpa using
      (Submodule.zero_mem
        (Submodule.span ℤ
          (Set.range fun J : {J : Subgroup H0 // β.ker ≤ J ∧ J < ⊤} ↦
            ⟪(Subgroup.characterRingInduction J.1 (1 : R(J.1)) : H0 → ℂ), (ξ : H0 → ℂ)⟫)))
  · intro η₁ η₂ hη₁ hη₂
    -- Additivity of the pairing linear map preserves target-span membership.
    simpa using
      (Submodule.add_mem
        (Submodule.span ℤ
          (Set.range fun J : {J : Subgroup H0 // β.ker ≤ J ∧ J < ⊤} ↦
            ⟪(Subgroup.characterRingInduction J.1 (1 : R(J.1)) : H0 → ℂ), (ξ : H0 → ℂ)⟫))
        hη₁ hη₂)
  · intro m η' hη'
    -- The target span is a `ℤ`-submodule, so integer scalar multiples stay inside it.
    simpa using
      (Submodule.smul_mem
        (Submodule.span ℤ
          (Set.range fun J : {J : Subgroup H0 // β.ker ≤ J ∧ J < ⊤} ↦
            ⟪(Subgroup.characterRingInduction J.1 (1 : R(J.1)) : H0 → ℂ), (ξ : H0 → ℂ)⟫))
        m hη')

/-- Helper for Remark 11-11.1-3: once a scalar pairing lies in the `ℤ`-span of the proper
overgroup induced-trivial pairings above `β.ker`, the local proper-branch theorem packages the
whole span witness into a single `n`-multiple. -/
private theorem overgroup_pairing_span_divisible_of_local_proper_branch
    (X : Finset (Subgroup G))
    (hXelem : ∀ H : Subgroup G, H ∈ X ↔ IsElementary H)
    {x : (H : X) → R(H.1)} {t : elementary_coherence_target X hXelem} {n : ℤ}
    (hdx : elementary_coherence_defect X hXelem x = n • t)
    (H : X)
    (sH : ((J : (Finset.univ : Finset (Subgroup H.1))) → R(J.1)) →ₗ[ℤ] R(H.1))
    (hsH : Function.LeftInverse sH
      (Representation.characterRingRestriction (Finset.univ : Finset (Subgroup H.1))).toLinearMap)
    (hproper :
      ∀ (J : Subgroup H.1) (hJ : J < ⊤) (α : J →* ℂˣ),
        let KX : X := ⟨J.map H.1.subtype,
          (hXelem (J.map H.1.subtype)).2 <|
            isElementary_of_mulEquiv_local
              (J.equivMapOfInjective H.1.subtype H.1.subtype_injective)
              (subgroup_isElementary_of_isElementary_local J ((hXelem H.1).1 H.2))⟩
        ∃ c : ℤ, linear_character_pairing_int H.1 J α (x KX) = n * c)
    (β : H.1 →* ℂˣ) {z : ℂ} :
    let XH : Finset (Subgroup H.1) := Finset.univ
    let ψH : (J : XH) → R(J.1) := fun J ↦
      Subgroup.characterRingTransport
        (J.1.equivMapOfInjective H.1.subtype H.1.subtype_injective)
        (x ⟨J.1.map H.1.subtype,
          (hXelem (J.1.map H.1.subtype)).2 <|
            isElementary_of_mulEquiv_local
              (J.1.equivMapOfInjective H.1.subtype H.1.subtype_injective)
              (subgroup_isElementary_of_isElementary_local J.1 ((hXelem H.1).1 H.2))⟩)
    let ξH : R(H.1) := sH ψH
    z ∈ Submodule.span ℤ
        (Set.range fun J : {J : Subgroup H.1 // β.ker ≤ J ∧ J < ⊤} ↦
          ⟪(Subgroup.characterRingInduction J.1 (1 : R(J.1)) : H.1 → ℂ), (ξH : H.1 → ℂ)⟫) →
      ∃ b : ℤ, z = algebraMap ℤ ℂ (n * b) := by
  classical
  dsimp
  intro hz
  obtain ⟨S, a, hS, ha⟩ :=
    exists_overgroup_finset_sum_of_mem_span_pairings β (sH ψH) hz
  obtain ⟨b, hb⟩ :=
    interval_overgroup_pairing_sum_divisible_of_local_proper_branch
      X hXelem hdx H sH hsH hproper S a (fun J hJ ↦ (hS J hJ).2)
  -- Reuse the finite-sum packaging from the span witness and then close the whole sum at once.
  exact ⟨b, ha.trans hb⟩

/-- Helper for Remark 11-11.1-3: once a quotient-side element lies in the `ℤ`-span of proper
induced-trivial quotient characters, pairing its pullback against the local test character is an
`n`-multiple by the proper-branch theorem on ambient overgroups of the kernel. -/
private theorem quotient_pullback_pairing_divisible_of_quotient_induced_trivial_span
    (X : Finset (Subgroup G))
    (hXelem : ∀ H : Subgroup G, H ∈ X ↔ IsElementary H)
    {x : (H : X) → R(H.1)} {t : elementary_coherence_target X hXelem} {n : ℤ}
    (hdx : elementary_coherence_defect X hXelem x = n • t)
    (H : X)
    (sH : ((J : (Finset.univ : Finset (Subgroup H.1))) → R(J.1)) →ₗ[ℤ] R(H.1))
    (hsH : Function.LeftInverse sH
      (Representation.characterRingRestriction (Finset.univ : Finset (Subgroup H.1))).toLinearMap)
    (hproper :
      ∀ (J : Subgroup H.1) (hJ : J < ⊤) (α : J →* ℂˣ),
        let KX : X := ⟨J.map H.1.subtype,
          (hXelem (J.map H.1.subtype)).2 <|
            isElementary_of_mulEquiv_local
              (J.equivMapOfInjective H.1.subtype H.1.subtype_injective)
              (subgroup_isElementary_of_isElementary_local J ((hXelem H.1).1 H.2))⟩
        ∃ c : ℤ, linear_character_pairing_int H.1 J α (x KX) = n * c)
    (β : H.1 →* ℂˣ) {η : R(H.1 ⧸ β.ker)}
    (hη :
      η ∈ Submodule.span ℤ
        (Set.range fun L : {L : Subgroup (H.1 ⧸ β.ker) // L < ⊤} ↦
          Subgroup.characterRingInduction L.1 (1 : R(L.1)))) :
    let XH : Finset (Subgroup H.1) := Finset.univ
    let ψH : (J : XH) → R(J.1) := fun J ↦
      Subgroup.characterRingTransport
        (J.1.equivMapOfInjective H.1.subtype H.1.subtype_injective)
        (x ⟨J.1.map H.1.subtype,
          (hXelem (J.1.map H.1.subtype)).2 <|
            isElementary_of_mulEquiv_local
              (J.1.equivMapOfInjective H.1.subtype H.1.subtype_injective)
              (subgroup_isElementary_of_isElementary_local J.1 ((hXelem H.1).1 H.2))⟩)
    let ξH : R(H.1) := sH ψH
    ∃ b : ℤ,
      quotient_pullback_pairing_linearMap β ξH η = algebraMap ℤ ℂ (n * b) := by
  classical
  let ψH : (J : (Finset.univ : Finset (Subgroup H.1))) → R(J.1) := fun J ↦
    Subgroup.characterRingTransport
      (J.1.equivMapOfInjective H.1.subtype H.1.subtype_injective)
      (x ⟨J.1.map H.1.subtype,
        (hXelem (J.1.map H.1.subtype)).2 <|
          isElementary_of_mulEquiv_local
            (J.1.equivMapOfInjective H.1.subtype H.1.subtype_injective)
            (subgroup_isElementary_of_isElementary_local J.1 ((hXelem H.1).1 H.2))⟩)
  let ξH : R(H.1) := sH ψH
  have hz :
      quotient_pullback_pairing_linearMap β ξH η ∈
        Submodule.span ℤ
          (Set.range fun J : {J : Subgroup H.1 // β.ker ≤ J ∧ J < ⊤} ↦
            ⟪(Subgroup.characterRingInduction J.1 (1 : R(J.1)) : H.1 → ℂ),
              (ξH : H.1 → ℂ)⟫) := by
    -- Push the quotient-side span witness through the pullback pairing so the ambient proper
    -- overgroup packaging theorem can consume it directly.
    exact
      quotient_pullback_pairing_mem_span_overgroups_of_mem_span_induced_trivial
        β ξH hη
  -- The local proper-branch theorem now packages the ambient overgroup span witness into one
  -- integer multiple of `n`.
  simpa [ψH, ξH] using
    overgroup_pairing_span_divisible_of_local_proper_branch
      X hXelem hdx H sH hsH hproper β
      (z := quotient_pullback_pairing_linearMap β ξH η) hz

/-- Helper for Remark 11-11.1-3: if the faithful quotient top layer on `H / β.ker` is already
known to lie in the `ℤ`-span of proper induced-trivial quotient characters, then the whole
faithful cyclic layer pairing upstairs is an `n`-multiple. -/
private theorem faithful_cyclic_layer_pairing_divisible_of_quotient_induced_trivial_span
    (X : Finset (Subgroup G))
    (hXelem : ∀ H : Subgroup G, H ∈ X ↔ IsElementary H)
    {x : (H : X) → R(H.1)} {t : elementary_coherence_target X hXelem} {n : ℤ}
    (hdx : elementary_coherence_defect X hXelem x = n • t)
    (H : X)
    (sH : ((J : (Finset.univ : Finset (Subgroup H.1))) → R(J.1)) →ₗ[ℤ] R(H.1))
    (hsH : Function.LeftInverse sH
      (Representation.characterRingRestriction (Finset.univ : Finset (Subgroup H.1))).toLinearMap)
    (hproper :
      ∀ (J : Subgroup H.1) (hJ : J < ⊤) (α : J →* ℂˣ),
        let KX : X := ⟨J.map H.1.subtype,
          (hXelem (J.map H.1.subtype)).2 <|
            isElementary_of_mulEquiv_local
              (J.equivMapOfInjective H.1.subtype H.1.subtype_injective)
              (subgroup_isElementary_of_isElementary_local J ((hXelem H.1).1 H.2))⟩
        ∃ c : ℤ, linear_character_pairing_int H.1 J α (x KX) = n * c)
    (β : H.1 →* ℂˣ)
    (hη :
      let βq : (H.1 ⧸ β.ker) →* ℂˣ :=
        QuotientGroup.lift β.ker β (show β.ker ≤ β.ker from le_rfl)
      let η : R(H.1 ⧸ β.ker) :=
        (β.ker.index : ℤ) • (1 : R(H.1 ⧸ β.ker)) +
          ∑ γ in ((Finset.univ.erase βq).filter fun γ => γ.ker = ⊥),
            ((γ.toCharacterRing - 1 : R(H.1 ⧸ β.ker)))
      η ∈ Submodule.span ℤ
        (Set.range fun L : {L : Subgroup (H.1 ⧸ β.ker) // L < ⊤} ↦
          Subgroup.characterRingInduction L.1 (1 : R(L.1)))) :
    let XH : Finset (Subgroup H.1) := Finset.univ
    let ψH : (J : XH) → R(J.1) := fun J ↦
      Subgroup.characterRingTransport
        (J.1.equivMapOfInjective H.1.subtype H.1.subtype_injective)
        (x ⟨J.1.map H.1.subtype,
          (hXelem (J.1.map H.1.subtype)).2 <|
            isElementary_of_mulEquiv_local
              (J.1.equivMapOfInjective H.1.subtype H.1.subtype_injective)
              (subgroup_isElementary_of_isElementary_local J.1 ((hXelem H.1).1 H.2))⟩)
    let ξH : R(H.1) := sH ψH
    ∃ bC : ℤ,
      (β.ker.index : ℂ) * ⟪((1 : R(H.1)) : H.1 → ℂ), (ξH : H.1 → ℂ)⟫ +
        ∑ γ in
            ((Finset.univ.erase
                (QuotientGroup.lift β.ker β (show β.ker ≤ β.ker from le_rfl))).filter
              fun γ => γ.ker = ⊥),
            ⟪((((γ.comp (QuotientGroup.mk' β.ker)).toCharacterRing - 1 : R(H.1)) :
                  H.1 → ℂ),
                (ξH : H.1 → ℂ)⟫ =
          algebraMap ℤ ℂ (n * bC) := by
  classical
  let ψH : (J : (Finset.univ : Finset (Subgroup H.1))) → R(J.1) := fun J ↦
    Subgroup.characterRingTransport
      (J.1.equivMapOfInjective H.1.subtype H.1.subtype_injective)
      (x ⟨J.1.map H.1.subtype,
        (hXelem (J.1.map H.1.subtype)).2 <|
          isElementary_of_mulEquiv_local
            (J.1.equivMapOfInjective H.1.subtype H.1.subtype_injective)
            (subgroup_isElementary_of_isElementary_local J.1 ((hXelem H.1).1 H.2))⟩)
  let ξH : R(H.1) := sH ψH
  let βq : (H.1 ⧸ β.ker) →* ℂˣ :=
    QuotientGroup.lift β.ker β (show β.ker ≤ β.ker from le_rfl)
  let η : R(H.1 ⧸ β.ker) :=
    (β.ker.index : ℤ) • (1 : R(H.1 ⧸ β.ker)) +
      ∑ γ in ((Finset.univ.erase βq).filter fun γ => γ.ker = ⊥),
        ((γ.toCharacterRing - 1 : R(H.1 ⧸ β.ker)))
  obtain ⟨bC, hbC⟩ :=
    quotient_pullback_pairing_divisible_of_quotient_induced_trivial_span
      X hXelem hdx H sH hsH hproper (β := β) (η := η) hη
  refine ⟨bC, ?_⟩
  -- Rewrite the faithful cyclic layer as the pullback pairing of the quotient-side faithful block
  -- and then apply the packaged quotient-span witness.
  calc
    (β.ker.index : ℂ) * ⟪((1 : R(H.1)) : H.1 → ℂ), (ξH : H.1 → ℂ)⟫ +
        ∑ γ in ((Finset.univ.erase βq).filter fun γ => γ.ker = ⊥),
          ⟪((((γ.comp (QuotientGroup.mk' β.ker)).toCharacterRing - 1 : R(H.1)) :
                H.1 → ℂ),
              (ξH : H.1 → ℂ)⟫ =
      quotient_pullback_pairing_linearMap β ξH η := by
        simpa [βq, η, ξH] using
          faithful_quotient_top_layer_eq_quotient_pullback_pairing
            (β := β)
            (ξ := ξH)
    _ = algebraMap ℤ ℂ (n * bC) := hbC

/-- Helper for Remark 11-11.1-3: in the equality branch `δ.ker = M`, the faithful cyclic layer is
already reduced to the distinguished ambient difference witness. This packages that reduction so
the remaining blocker is stated at the exact pairing level used by the source proof. -/
private theorem prime_coatom_kernel_eq_branch_of_difference_divisible
    {H0 : Type*} [Group H0] [Finite H0] {n : ℤ}
    (δ : H0 →* ℂˣ) (hδ : δ ≠ 1)
    (M : Subgroup H0) [M.Normal]
    (ξH : R(H0))
    (hEq : δ.ker = M)
    (hprime : (Nat.card (H0 ⧸ M)).Prime)
    (hMpair :
      ∃ bM : ℤ,
        ⟪(Subgroup.characterRingInduction M (1 : R(M)) : H0 → ℂ), (ξH : H0 → ℂ)⟫ =
          algebraMap ℤ ℂ (n * bM))
    (hdiff :
      ∃ bδ : ℤ,
        ⟪((((δ.toCharacterRing - 1 : R(H0)) : H0 → ℂ)), (ξH : H0 → ℂ)⟫ =
          algebraMap ℤ ℂ (n * bδ)) :
    ∃ bC : ℤ,
      (δ.ker.index : ℂ) * ⟪((1 : R(H0)) : H0 → ℂ), (ξH : H0 → ℂ)⟫ +
        ∑ γ in ((Finset.univ.erase
            (QuotientGroup.lift δ.ker δ (show δ.ker ≤ δ.ker from le_rfl))).filter
          fun γ => γ.ker = ⊥),
          ⟪((((γ.comp (QuotientGroup.mk' δ.ker)).toCharacterRing - 1 : R(H0)) :
                H0 → ℂ),
              (ξH : H0 → ℂ)⟫ =
        algebraMap ℤ ℂ (n * bC) := by
  -- Route correction: in the kernel-equality branch, the owner theorem is already available
  -- earlier in the file; only the distinguished-difference witness still has to be supplied.
  exact
    faithful_cyclic_layer_of_kernel_eq_chosen_coatom_of_difference_divisible
      δ hδ M ξH hEq hprime hMpair hdiff

/-- Helper for Remark 11-11.1-3: mapping an overgroup of `K` into `H0 ⧸ K` and then pulling it
back along the quotient map recovers the original overgroup. -/
private theorem quotient_comap_map_eq_of_le
    {H0 : Type*} [Group H0]
    (K M : Subgroup H0) (hKM : K ≤ M) :
    Subgroup.comap (QuotientGroup.mk' K) (M.map (QuotientGroup.mk' K)) = M := by
  ext x
  constructor
  · intro hx
    change QuotientGroup.mk' K x ∈ M.map (QuotientGroup.mk' K) at hx
    rcases hx with ⟨m, hm, hmx⟩
    rcases (QuotientGroup.mk'_eq_mk' (N := K)).mp hmx with ⟨z, hz, hxz⟩
    -- The quotient equality differs by an element of `K`, hence by an element of `M`.
    have hzM : z ∈ M := hKM hz
    have hxM : x * z ∈ M := by simpa [hxz] using hm
    have hxzM : x ∈ M := by
      rw [← mul_right_inv z, ← mul_assoc]
      exact M.mul_mem hxM (M.inv_mem hzM)
    exact hxzM
  · intro hx
    -- Any element of `M` maps to the corresponding quotient subgroup by definition.
    exact ⟨x, hx, rfl⟩

/-- Helper for Remark 11-11.1-3: quotienting `H0 ⧸ K` by the image of an overgroup `M`
has the same cardinality as quotienting `H0` directly by `M`. -/
private theorem quotient_map_card_eq_quotient_card
    {H0 : Type*} [Group H0] [Finite H0]
    (K M : Subgroup H0) (hKM : K ≤ M) :
    Nat.card (((H0 ⧸ K) ⧸ M.map (QuotientGroup.mk' K))) = Nat.card (H0 ⧸ M) := by
  let L : Subgroup (H0 ⧸ K) := M.map (QuotientGroup.mk' K)
  have hcard :
      Fintype.card (H0 ⧸ Subgroup.comap (QuotientGroup.mk' K) L) =
        Fintype.card ((H0 ⧸ K) ⧸ L) := by
    exact
      Fintype.card_congr
        (QuotientMonomialReduction.quotient_comap_leftCosetEquiv_local
          (Q := H0) (N := K) L)
  -- The quotient-comap equivalence identifies the iterated quotient with the direct quotient.
  simpa [Nat.card_eq_fintype_card, L, quotient_comap_map_eq_of_le K M hKM] using hcard.symm

/-- Helper for Remark 11-11.1-3: if `H0 ⧸ M` has prime cardinality, then the iterated quotient
`(H0 ⧸ K) ⧸ M.map (mk' K)` also has prime cardinality. -/
private theorem quotient_map_prime_card_of_prime_quotient
    {H0 : Type*} [Group H0] [Finite H0]
    (K M : Subgroup H0) (hKM : K ≤ M)
    (hprime : (Nat.card (H0 ⧸ M)).Prime) :
    (Nat.card (((H0 ⧸ K) ⧸ M.map (QuotientGroup.mk' K)))).Prime := by
  -- Replace the iterated quotient cardinality by the direct quotient cardinality.
  simpa [quotient_map_card_eq_quotient_card K M hKM] using hprime

/-- Helper for Remark 11-11.1-3: the iterated quotient character obtained from
`((H0 ⧸ δ.ker) ⧸ M.map (mk' δ.ker))` pulls back to the same ambient character as the direct
quotient character transported through Noether's third isomorphism. -/
private theorem iterated_quotient_character_pullback_eq_direct_pullback
    {H0 : Type*} [Group H0] [Finite H0]
    (δ : H0 →* ℂˣ)
    (M : Subgroup H0) [M.Normal]
    (hδker_le_M : δ.ker ≤ M)
    (β : ((H0 ⧸ δ.ker) ⧸ M.map (QuotientGroup.mk' δ.ker)) →* ℂˣ) :
    (β.comp (QuotientGroup.mk' (M.map (QuotientGroup.mk' δ.ker)))).comp
        (QuotientGroup.mk' δ.ker) =
      (β.comp (QuotientGroup.quotientQuotientEquivQuotient δ.ker M hδker_le_M).symm.toMonoidHom).comp
        (QuotientGroup.mk' M) := by
  ext x
  let e : ((H0 ⧸ δ.ker) ⧸ M.map (QuotientGroup.mk' δ.ker)) ≃* H0 ⧸ M :=
    QuotientGroup.quotientQuotientEquivQuotient δ.ker M hδker_le_M
  have he :
      e ((QuotientGroup.mk' (M.map (QuotientGroup.mk' δ.ker))) ((QuotientGroup.mk' δ.ker) x)) =
        QuotientGroup.mk' M x := by
    -- The third-isomorphism comparison sends the iterated quotient class of `x` to its direct
    -- quotient class modulo `M`.
    simpa [e] using
      (QuotientGroup.quotientQuotientEquivQuotientAux_mk_mk
        (N := δ.ker) (M := M) hδker_le_M x)
  have he_symm :
      e.symm (QuotientGroup.mk' M x) =
        (QuotientGroup.mk' (M.map (QuotientGroup.mk' δ.ker))) ((QuotientGroup.mk' δ.ker) x) := by
    -- Apply the inverse equivalence to the direct quotient class to recover the iterated one.
    simpa using congrArg e.symm he
  -- Evaluating either transported character on `x` gives the same scalar.
  simp [MonoidHom.comp_apply, e, he_symm]

/-- Helper for Remark 11-11.1-3: after applying the quotient pullback pairing to an iterated
quotient-character difference, Noether's third isomorphism rewrites the summand as the ambient
difference term attached to the corresponding direct quotient character on `H0 ⧸ M`. -/
private theorem quotient_pullback_pairing_linearMap_difference_via_third_iso
    {H0 : Type*} [Group H0] [Finite H0]
    (δ : H0 →* ℂˣ)
    (M : Subgroup H0) [M.Normal]
    (hδker_le_M : δ.ker ≤ M)
    (ξH : R(H0))
    (β : ((H0 ⧸ δ.ker) ⧸ M.map (QuotientGroup.mk' δ.ker)) →* ℂˣ) :
    quotient_pullback_pairing_linearMap δ ξH
        (((β.comp (QuotientGroup.mk' (M.map (QuotientGroup.mk' δ.ker)))).toCharacterRing - 1 :
            R(H0 ⧸ δ.ker))) =
      ⟪((((((β.comp (QuotientGroup.quotientQuotientEquivQuotient δ.ker M hδker_le_M).symm.toMonoidHom).comp
            (QuotientGroup.mk' M)).toCharacterRing - 1 : R(H0)) : H0 → ℂ)),
          (ξH : H0 → ℂ)⟫ := by
  -- First rewrite the quotient-pullback pairing as the ambient erased-difference term for the
  -- iterated quotient character.
  rw [quotient_pullback_pairing_linearMap_difference]
  -- Then transport the pulled-back character itself across the third-isomorphism comparison.
  simp [iterated_quotient_character_pullback_eq_direct_pullback (δ := δ) (M := M) hδker_le_M β]

/-- Helper for Remark 11-11.1-3: the mapped coatom induced-trivial term in the strict branch
pulls back to the ambient coatom induced-trivial pairing. -/
private theorem strict_branch_mapped_coatom_pullback_pairing_eq_ambient_coatom_pairing
    {H0 : Type*} [Group H0] [Finite H0]
    (δ : H0 →* ℂˣ)
    (M : Subgroup H0)
    (hδker_le_M : δ.ker ≤ M)
    (ξH : R(H0)) :
    quotient_pullback_pairing_linearMap δ ξH
        (Subgroup.characterRingInduction
          (M.map (QuotientGroup.mk' δ.ker))
          (1 : R(M.map (QuotientGroup.mk' δ.ker)))) =
      ⟪(Subgroup.characterRingInduction M (1 : R(M)) : H0 → ℂ), (ξH : H0 → ℂ)⟫ := by
  -- Rewrite the quotient induced-trivial term through the comap/pullback identification so the
  -- existing ambient coatom witness can be reused without changing owners.
  simpa [quotient_comap_map_eq_of_le δ.ker M hδker_le_M] using
    quotient_pullback_pairing_linearMap_induced_trivial
      (β := δ)
      (ξ := ξH)
      (L := M.map (QuotientGroup.mk' δ.ker))

/-- Helper for Remark 11-11.1-3: transporting the iterated strict-branch quotient-difference
family across Noether's third isomorphism turns the whole sum into the already packaged prime
quotient difference sum. -/
private theorem strict_branch_iterated_difference_term_divisible
    {H0 : Type*} [Group H0] [Finite H0] {n : ℤ}
    (δ : H0 →* ℂˣ)
    (M : Subgroup H0) [M.Normal]
    (hδker_lt_M : δ.ker < M)
    (hprime : (Nat.card (H0 ⧸ M)).Prime)
    (ξH : R(H0))
    (hMpair :
      ∃ bM : ℤ,
        ⟪(Subgroup.characterRingInduction M (1 : R(M)) : H0 → ℂ), (ξH : H0 → ℂ)⟫ =
          algebraMap ℤ ℂ (n * bM))
    (hsmaller :
      ∀ ε : H0 →* ℂˣ, ε ≠ 1 → ε.ker.index < δ.ker.index →
        ∃ bC : ℤ,
          (ε.ker.index : ℂ) * ⟪((1 : R(H0)) : H0 → ℂ), (ξH : H0 → ℂ)⟫ +
            ∑ γ in
                ((Finset.univ.erase
                    (QuotientGroup.lift ε.ker ε (show ε.ker ≤ ε.ker from le_rfl))).filter
                  fun γ => γ.ker = ⊥),
                ⟪((((γ.comp (QuotientGroup.mk' ε.ker)).toCharacterRing - 1 : R(H0)) :
                      H0 → ℂ),
                    (ξH : H0 → ℂ)⟫ =
              algebraMap ℤ ℂ (n * bC))
    (β : ((H0 ⧸ δ.ker) ⧸ M.map (QuotientGroup.mk' δ.ker)) →* ℂˣ) :
    ∃ bβ : ℤ,
      quotient_pullback_pairing_linearMap δ ξH
          (((β.comp (QuotientGroup.mk' (M.map (QuotientGroup.mk' δ.ker)))).toCharacterRing - 1 :
              R(H0 ⧸ δ.ker))) =
        algebraMap ℤ ℂ (n * bβ) := by
  classical
  let e : ((H0 ⧸ δ.ker) ⧸ M.map (QuotientGroup.mk' δ.ker)) ≃* H0 ⧸ M :=
    QuotientGroup.quotientQuotientEquivQuotient δ.ker M hδker_lt_M.le
  let β' : (H0 ⧸ M) →* ℂˣ := β.comp e.symm.toMonoidHom
  by_cases hβ : β = 1
  · refine ⟨0, ?_⟩
    -- The trivial iterated quotient character contributes the zero difference term.
    rw [hβ]
    simp
  · have hβ' : β' ≠ 1 := by
      intro hβ'
      apply hβ
      ext x
      -- Transporting the direct quotient equality back across the third-isomorphism equivalence
      -- recovers the original iterated quotient character.
      have hβ'_eval :=
        congrFun (congrArg MonoidHom.toFun hβ') (e x)
      simpa [β', e] using hβ'_eval
    obtain ⟨bβ, hbβ⟩ :=
      prime_coatom_lift_difference_pairing_divisible_from_smaller_kernel_package
        (δ := δ)
        (M := M)
        hδker_lt_M
        hprime
        ξH
        hMpair
        hsmaller
        β'
        hβ'
    refine ⟨bβ, ?_⟩
    -- Rewrite the iterated quotient summand as the direct prime-quotient lift summand and then
    -- reuse the already packaged strict-branch witness for that direct character.
    calc
      quotient_pullback_pairing_linearMap δ ξH
          (((β.comp (QuotientGroup.mk' (M.map (QuotientGroup.mk' δ.ker)))).toCharacterRing - 1 :
              R(H0 ⧸ δ.ker))) =
        ⟪((((β'.comp (QuotientGroup.mk' M)).toCharacterRing - 1 : R(H0)) : H0 → ℂ)),
            (ξH : H0 → ℂ)⟫ := by
              simpa [β', e] using
                quotient_pullback_pairing_linearMap_difference_via_third_iso
                  (δ := δ)
                  (M := M)
                  hδker_lt_M.le
                  ξH
                  β
      _ = algebraMap ℤ ℂ (n * bβ) := hbβ

/-- Helper for Remark 11-11.1-3: transporting the iterated strict-branch quotient-difference
family across Noether's third isomorphism turns the whole sum into the already packaged prime
quotient difference sum. -/
private theorem strict_branch_iterated_difference_sum_divisible
    {H0 : Type*} [Group H0] [Finite H0] {n : ℤ}
    (δ : H0 →* ℂˣ)
    (M : Subgroup H0) [M.Normal]
    (hδker_lt_M : δ.ker < M)
    (hprime : (Nat.card (H0 ⧸ M)).Prime)
    (ξH : R(H0))
    (hprime_sum :
      ∃ bΣ : ℤ,
        ∑ β in ((Finset.univ.erase (1 : (H0 ⧸ M) →* ℂˣ)).filter fun β => β.ker = ⊥),
          ⟪((((β.comp (QuotientGroup.mk' M)).toCharacterRing - 1 : R(H0)) : H0 → ℂ),
              (ξH : H0 → ℂ)⟫ =
          algebraMap ℤ ℂ (n * bΣ)) :
    ∃ bΣ : ℤ,
      ∑ β : ((H0 ⧸ δ.ker) ⧸ M.map (QuotientGroup.mk' δ.ker)) →* ℂˣ,
        quotient_pullback_pairing_linearMap δ ξH
          (((β.comp (QuotientGroup.mk' (M.map (QuotientGroup.mk' δ.ker)))).toCharacterRing - 1 :
              R(H0 ⧸ δ.ker))) =
        algebraMap ℤ ℂ (n * bΣ) := by
  classical
  let e : ((H0 ⧸ δ.ker) ⧸ M.map (QuotientGroup.mk' δ.ker)) ≃* H0 ⧸ M :=
    QuotientGroup.quotientQuotientEquivQuotient δ.ker M hδker_lt_M.le
  let eχ :
      ((H0 ⧸ M) →* ℂˣ) ≃
        (((H0 ⧸ δ.ker) ⧸ M.map (QuotientGroup.mk' δ.ker)) →* ℂˣ) where
    toFun := fun β ↦ β.comp e.toMonoidHom
    invFun := fun β ↦ β.comp e.symm.toMonoidHom
    left_inv := by
      intro β
      ext x
      rfl
    right_inv := by
      intro β
      ext x
      rfl
  let iterTerm :
      (((H0 ⧸ δ.ker) ⧸ M.map (QuotientGroup.mk' δ.ker)) →* ℂˣ) → ℂ := fun β ↦
        quotient_pullback_pairing_linearMap δ ξH
          (((β.comp (QuotientGroup.mk' (M.map (QuotientGroup.mk' δ.ker)))).toCharacterRing - 1 :
              R(H0 ⧸ δ.ker)))
  let directTerm : ((H0 ⧸ M) →* ℂˣ) → ℂ := fun β ↦
    ⟪((((β.comp (QuotientGroup.mk' M)).toCharacterRing - 1 : R(H0)) : H0 → ℂ),
        (ξH : H0 → ℂ)⟫
  have htransport :
      ∀ β : (H0 ⧸ M) →* ℂˣ,
        iterTerm (eχ β) = directTerm β := by
    intro β
    -- Transport each iterated quotient summand through the third-isomorphism equivalence so it
    -- becomes exactly the ambient prime-quotient lift summand.
    simpa [iterTerm, directTerm, eχ, e] using
      quotient_pullback_pairing_linearMap_difference_via_third_iso
        (δ := δ)
        (M := M)
        hδker_lt_M.le
        ξH
        (β.comp e.toMonoidHom)
  have hsum_transport :
      ∑ β : ((H0 ⧸ δ.ker) ⧸ M.map (QuotientGroup.mk' δ.ker)) →* ℂˣ, iterTerm β =
        ∑ β : (H0 ⧸ M) →* ℂˣ, directTerm β := by
    -- Reindex the iterated quotient character family by the third-isomorphism equivalence.
    exact Fintype.sum_equiv eχ directTerm iterTerm htransport
  have hsplit :
      ∑ β : (H0 ⧸ M) →* ℂˣ, directTerm β =
        directTerm (1 : (H0 ⧸ M) →* ℂˣ) +
          ∑ β in Finset.univ.erase (1 : (H0 ⧸ M) →* ℂˣ), directTerm β := by
    -- Isolate the trivial quotient character so the remaining family matches the packaged
    -- prime-quotient sum.
    simpa [directTerm] using
      (Finset.sum_erase_add
        (s := Finset.univ)
        (a := (1 : (H0 ⧸ M) →* ℂˣ))
        (by simp)).symm
  have hone :
      directTerm (1 : (H0 ⧸ M) →* ℂˣ) = 0 := by
    -- The trivial quotient character contributes the zero difference term.
    simp [directTerm]
  rcases hprime_sum with ⟨bΣ, hbΣ⟩
  refine ⟨bΣ, ?_⟩
  calc
    ∑ β : ((H0 ⧸ δ.ker) ⧸ M.map (QuotientGroup.mk' δ.ker)) →* ℂˣ, iterTerm β =
        ∑ β : (H0 ⧸ M) →* ℂˣ, directTerm β := hsum_transport
    _ =
        directTerm (1 : (H0 ⧸ M) →* ℂˣ) +
          ∑ β in Finset.univ.erase (1 : (H0 ⧸ M) →* ℂˣ), directTerm β := hsplit
    _ =
        ∑ β in Finset.univ.erase (1 : (H0 ⧸ M) →* ℂˣ), directTerm β := by
          rw [hone]
          simp
    _ =
        ∑ β in ((Finset.univ.erase (1 : (H0 ⧸ M) →* ℂˣ)).filter fun β => β.ker = ⊥),
          directTerm β := by
            symm
            simpa [prime_quotient_faithful_filter_eq_erase_one (M := M) hprime]
    _ = algebraMap ℤ ℂ (n * bΣ) := hbΣ

/-- Helper for Remark 11-11.1-3: the previously attempted quotient-ring reassembly in the strict
branch is impossible. Evaluating it at the identity class would force `δ.ker.index = M.index`,
contradicting `δ.ker < M`. -/
private theorem strict_mapped_coatom_ring_reassembly_impossible
    {H0 : Type*} [Group H0] [Finite H0]
    (δ : H0 →* ℂˣ)
    (M : Subgroup H0) [M.Normal]
    (hδker_lt_M : δ.ker < M)
    :
    let δq : (H0 ⧸ δ.ker) →* ℂˣ :=
      QuotientGroup.lift δ.ker δ (show δ.ker ≤ δ.ker from le_rfl)
    let Mq : Subgroup (H0 ⧸ δ.ker) := M.map (QuotientGroup.mk' δ.ker)
    ¬ (((δ.ker.index : ℤ) • (1 : R(H0 ⧸ δ.ker)) +
        ∑ γ in ((Finset.univ.erase δq).filter fun γ => γ.ker = ⊥),
          ((γ.toCharacterRing - 1 : R(H0 ⧸ δ.ker)))) =
      Subgroup.characterRingInduction Mq (1 : R(Mq)) +
        ∑ β in ((Finset.univ.erase (1 : (((H0 ⧸ δ.ker) ⧸ Mq) →* ℂˣ))).filter
            fun β => β.ker = ⊥),
          ((β.comp (QuotientGroup.mk' Mq)).toCharacterRing - 1 : R(H0 ⧸ δ.ker))) := by
  classical
  let δq : (H0 ⧸ δ.ker) →* ℂˣ :=
    QuotientGroup.lift δ.ker δ (show δ.ker ≤ δ.ker from le_rfl)
  let Mq : Subgroup (H0 ⧸ δ.ker) := M.map (QuotientGroup.mk' δ.ker)
  intro hreassembly
  have hMq_index : Mq.index = M.index := by
    -- The mapped overgroup has the same quotient cardinality, hence the same index, as `M`.
    rw [Mq.index_eq_card, M.index_eq_card]
    simpa [Mq] using quotient_map_card_eq_quotient_card δ.ker M hδker_lt_M.le
  have hEval :=
    congrArg (fun η : R(H0 ⧸ δ.ker) ↦ ((η : H0 ⧸ δ.ker → ℂ) 1)) hreassembly
  have hEq_complex : (δ.ker.index : ℂ) = M.index := by
    -- Every difference term vanishes at the identity, so only the index terms remain.
    have hEval' : (((δ.ker.index : ℤ) : ℂ)) = Mq.index := by
      simpa [δq, Mq, Subgroup.characterRingInduction_apply,
        Subgroup.inducedClassFunction_one_eq_index_mul_value, MonoidHom.toCharacterRing_apply]
        using hEval
    calc
      (δ.ker.index : ℂ) = (((δ.ker.index : ℤ) : ℂ)) := by simp
      _ = Mq.index := hEval'
      _ = M.index := by exact_mod_cast hMq_index
  have hEq : δ.ker.index = M.index := by
    exact_mod_cast hEq_complex
  exact (Nat.ne_of_lt (Subgroup.index_strictAnti hδker_lt_M)) hEq.symm

/-- Helper for Remark 11-11.1-3: every finite cyclic group is elementary. This keeps the strict
branch quotient-top-layer argument inside the dependency-closed Chapter 10 API. -/
private theorem isElementary_of_isCyclic_quotient_local
    {H0 : Type*} [Group H0] [Finite H0]
    (hcyc : IsCyclic H0) :
    IsElementary H0 := by
  -- Choose a prime larger than `|H0|`; then `H0 = H0 × ⊥` is a `p`-elementary decomposition.
  obtain ⟨p, hpge, hpprime⟩ := Nat.exists_infinite_primes (Nat.card H0 + 1)
  refine ⟨p, ⊤, ⊥, ?_⟩
  refine ⟨hpprime, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- The trivial `p`-group factor is finite.
    infer_instance
  · -- The cyclic factor is the whole group.
    simpa using (Subgroup.topEquiv : (⊤ : Subgroup H0) ≃* H0).isCyclic.2 hcyc
  · -- The chosen prime does not divide the cardinality of the cyclic factor.
    have hlt : Nat.card H0 < p := lt_of_lt_of_le (Nat.lt_succ_self _) hpge
    have hcard_top : Nat.card (⊤ : Subgroup H0) = Nat.card H0 :=
      Nat.card_congr Subgroup.topEquiv.toEquiv
    rw [Nat.Prime.coprime_iff_not_dvd hpprime, hcard_top]
    exact Nat.not_dvd_of_pos_of_lt Nat.card_pos hlt
  · -- The trivial subgroup is automatically a `p`-group.
    simpa using (IsPGroup.of_bot (p := p) : IsPGroup p (⊥ : Subgroup H0))
  · -- Centralizing the trivial subgroup is tautological.
    intro c hc y hy
    have hy1 : y = 1 := by simpa using hy
    simpa [hy1]
  · -- `⊤` and `⊥` are complementary.
    simpa using Subgroup.isComplement'_top_bot (G := H0)

/-- Helper for Remark 11-11.1-3: the strict-branch quotient-top-layer element already lies in
LinearRepresentations_Serre_1977's subgroup `R'` of the cyclic kernel quotient. The remaining blocker is therefore the
sharper upgrade from `R'` to the span of proper induced-trivial quotient characters. -/
private theorem faithful_quotient_top_layer_mem_elementaryLinearCharacterSpan_of_nontrivial_character
    {H0 : Type*} [Group H0] [Finite H0]
    (β : H0 →* ℂˣ) (hβ : β ≠ 1) :
    let βq : (H0 ⧸ β.ker) →* ℂˣ :=
      QuotientGroup.lift β.ker β (show β.ker ≤ β.ker from le_rfl)
    let η : R(H0 ⧸ β.ker) :=
      (β.ker.index : ℤ) • (1 : R(H0 ⧸ β.ker)) +
        ∑ γ in ((Finset.univ.erase βq).filter fun γ => γ.ker = ⊥),
          ((γ.toCharacterRing - 1 : R(H0 ⧸ β.ker)))
    η ∈ R'(H0 ⧸ β.ker) := by
  classical
  dsimp
  have hcyc : IsCyclic (H0 ⧸ β.ker) :=
    kernel_quotient_isCyclic_of_nontrivial_character β hβ
  have hElem : IsElementary (H0 ⧸ β.ker) :=
    isElementary_of_isCyclic_quotient_local hcyc
  -- On the cyclic kernel quotient, Chapter 10 already identifies LinearRepresentations_Serre_1977's subgroup with the full
  -- character ring, so the faithful top layer is automatically an `R'` element.
  rw [elementaryLinearCharacterSpan_eq_top_of_isElementary hElem]
  simp

/-- Helper for Remark 11-11.1-3: in the strict branch, the mapped-coatom block on the kernel
quotient already has pullback pairing divisible by `n`. This packages the coatom-induced term and
the transported iterated quotient-character family into one scalar witness before the residual
quotient correction is addressed. -/
private theorem strict_branch_mapped_coatom_block_pairing_divisible
    {H0 : Type*} [Group H0] [Finite H0] {n : ℤ}
    (δ : H0 →* ℂˣ)
    (M : Subgroup H0) [M.Normal]
    (hδker_lt_M : δ.ker < M)
    (hprime : (Nat.card (H0 ⧸ M)).Prime)
    (ξH : R(H0))
    (hMpair :
      ∃ bM : ℤ,
        ⟪(Subgroup.characterRingInduction M (1 : R(M)) : H0 → ℂ), (ξH : H0 → ℂ)⟫ =
          algebraMap ℤ ℂ (n * bM))
    (hprime_sum :
      ∃ bΣ : ℤ,
        ∑ β in ((Finset.univ.erase (1 : (H0 ⧸ M) →* ℂˣ)).filter fun β => β.ker = ⊥),
          ⟪((((β.comp (QuotientGroup.mk' M)).toCharacterRing - 1 : R(H0)) : H0 → ℂ),
              (ξH : H0 → ℂ)⟫ =
          algebraMap ℤ ℂ (n * bΣ)) :
    let Mq : Subgroup (H0 ⧸ δ.ker) := M.map (QuotientGroup.mk' δ.ker)
    let ηM : R(H0 ⧸ δ.ker) :=
      Subgroup.characterRingInduction Mq (1 : R(Mq)) -
        ∑ β : ((H0 ⧸ δ.ker) ⧸ Mq) →* ℂˣ,
          (((β.comp (QuotientGroup.mk' Mq)).toCharacterRing - 1 : R(H0 ⧸ δ.ker)))
    ∃ b : ℤ,
      quotient_pullback_pairing_linearMap δ ξH ηM = algebraMap ℤ ℂ (n * b) := by
  classical
  dsimp
  let Mq : Subgroup (H0 ⧸ δ.ker) := M.map (QuotientGroup.mk' δ.ker)
  have hmapped_pair :
      ∃ bM : ℤ,
        quotient_pullback_pairing_linearMap δ ξH
            (Subgroup.characterRingInduction Mq (1 : R(Mq))) =
          algebraMap ℤ ℂ (n * bM) := by
    rcases hMpair with ⟨bM, hbM⟩
    refine ⟨bM, ?_⟩
    -- Pull the mapped coatom back to the already controlled ambient coatom pairing.
    calc
      quotient_pullback_pairing_linearMap δ ξH
          (Subgroup.characterRingInduction Mq (1 : R(Mq))) =
        ⟪(Subgroup.characterRingInduction M (1 : R(M)) : H0 → ℂ), (ξH : H0 → ℂ)⟫ := by
            simpa [Mq] using
              strict_branch_mapped_coatom_pullback_pairing_eq_ambient_coatom_pairing
                (δ := δ)
                (M := M)
                hδker_lt_M.le
                ξH
      _ = algebraMap ℤ ℂ (n * bM) := hbM
  have hiterated_sum :
      ∃ bΣ : ℤ,
        ∑ β : ((H0 ⧸ δ.ker) ⧸ Mq) →* ℂˣ,
          quotient_pullback_pairing_linearMap δ ξH
            (((β.comp (QuotientGroup.mk' Mq)).toCharacterRing - 1 : R(H0 ⧸ δ.ker))) =
          algebraMap ℤ ℂ (n * bΣ) := by
    -- Transport the iterated quotient family back to the prime-quotient family on `H0 / M`.
    simpa [Mq] using
      strict_branch_iterated_difference_sum_divisible
        (δ := δ)
        (M := M)
        hδker_lt_M
        hprime
        ξH
        hprime_sum
  rcases hmapped_pair with ⟨bM, hbM⟩
  rcases hiterated_sum with ⟨bΣ, hbΣ⟩
  refine ⟨bM - bΣ, ?_⟩
  -- The mapped-coatom block is exactly the induced-trivial term minus the transported quotient
  -- family, so its pullback pairing is the difference of the two already packaged witnesses.
  calc
    quotient_pullback_pairing_linearMap δ ξH
        (Subgroup.characterRingInduction Mq (1 : R(Mq)) -
          ∑ β : ((H0 ⧸ δ.ker) ⧸ Mq) →* ℂˣ,
            (((β.comp (QuotientGroup.mk' Mq)).toCharacterRing - 1 : R(H0 ⧸ δ.ker)))) =
      quotient_pullback_pairing_linearMap δ ξH
          (Subgroup.characterRingInduction Mq (1 : R(Mq))) -
        ∑ β : ((H0 ⧸ δ.ker) ⧸ Mq) →* ℂˣ,
          quotient_pullback_pairing_linearMap δ ξH
            (((β.comp (QuotientGroup.mk' Mq)).toCharacterRing - 1 : R(H0 ⧸ δ.ker))) := by
          simp
    _ = algebraMap ℤ ℂ (n * bM) - algebraMap ℤ ℂ (n * bΣ) := by
          rw [hbM, hbΣ]
    _ = algebraMap ℤ ℂ (n * (bM - bΣ)) := by
          simp [Int.cast_mul, Int.cast_sub, sub_eq_add_neg, mul_add, mul_assoc]

/-- Helper for Remark 11-11.1-3: once every iterated strict-branch quotient-difference term is an
`n`-multiple, the whole iterated quotient-character family packages into a single `n`-multiple.
-/
private theorem strict_branch_iterated_quotient_sum_divisible_of_termwise
    {H0 : Type*} [Group H0] [Finite H0] {n : ℤ}
    (δ : H0 →* ℂˣ)
    (M : Subgroup H0) [M.Normal]
    (ξH : R(H0))
    (hterm :
      ∀ β : ((H0 ⧸ δ.ker) ⧸ M.map (QuotientGroup.mk' δ.ker)) →* ℂˣ,
        ∃ bβ : ℤ,
          quotient_pullback_pairing_linearMap δ ξH
              (((β.comp (QuotientGroup.mk' (M.map (QuotientGroup.mk' δ.ker)))).toCharacterRing -
                    1 :
                  R(H0 ⧸ δ.ker))) =
            algebraMap ℤ ℂ (n * bβ)) :
    ∃ bΣ : ℤ,
      ∑ β : ((H0 ⧸ δ.ker) ⧸ M.map (QuotientGroup.mk' δ.ker)) →* ℂˣ,
        quotient_pullback_pairing_linearMap δ ξH
          (((β.comp (QuotientGroup.mk' (M.map (QuotientGroup.mk' δ.ker)))).toCharacterRing - 1 :
              R(H0 ⧸ δ.ker))) =
        algebraMap ℤ ℂ (n * bΣ) := by
  classical
  -- Package the termwise strict-branch divisibility witnesses over the finite iterated quotient
  -- character family before reassembling the residual theorem.
  exact
    finset_sum_int_multiples
      (s := Finset.univ)
      (f := fun β : ((H0 ⧸ δ.ker) ⧸ M.map (QuotientGroup.mk' δ.ker)) →* ℂˣ ↦
        quotient_pullback_pairing_linearMap δ ξH
          (((β.comp (QuotientGroup.mk' (M.map (QuotientGroup.mk' δ.ker)))).toCharacterRing - 1 :
              R(H0 ⧸ δ.ker))))
      (n := n)
      (fun β _ ↦ hterm β)

/-- Helper for Remark 11-11.1-3: the iterated strict-branch quotient-character family is already
an `n`-multiple once each transported prime-quotient lift summand is fed through the
smaller-kernel package. -/
private theorem strict_branch_iterated_quotient_sum_divisible
    {H0 : Type*} [Group H0] [Finite H0] {n : ℤ}
    (δ : H0 →* ℂˣ)
    (M : Subgroup H0) [M.Normal]
    (hδker_lt_M : δ.ker < M)
    (hprime : (Nat.card (H0 ⧸ M)).Prime)
    (ξH : R(H0))
    (hMpair :
      ∃ bM : ℤ,
        ⟪(Subgroup.characterRingInduction M (1 : R(M)) : H0 → ℂ), (ξH : H0 → ℂ)⟫ =
          algebraMap ℤ ℂ (n * bM))
    (hsmaller :
      ∀ ε : H0 →* ℂˣ, ε ≠ 1 → ε.ker.index < δ.ker.index →
        ∃ bC : ℤ,
          (ε.ker.index : ℂ) * ⟪((1 : R(H0)) : H0 → ℂ), (ξH : H0 → ℂ)⟫ +
            ∑ γ in
                ((Finset.univ.erase
                    (QuotientGroup.lift ε.ker ε (show ε.ker ≤ ε.ker from le_rfl))).filter
                  fun γ => γ.ker = ⊥),
                ⟪((((γ.comp (QuotientGroup.mk' ε.ker)).toCharacterRing - 1 : R(H0)) :
                      H0 → ℂ),
                    (ξH : H0 → ℂ)⟫ =
              algebraMap ℤ ℂ (n * bC)) :
    ∃ bΣ : ℤ,
      ∑ β : ((H0 ⧸ δ.ker) ⧸ M.map (QuotientGroup.mk' δ.ker)) →* ℂˣ,
        quotient_pullback_pairing_linearMap δ ξH
          (((β.comp (QuotientGroup.mk' (M.map (QuotientGroup.mk' δ.ker)))).toCharacterRing - 1 :
              R(H0 ⧸ δ.ker))) =
        algebraMap ℤ ℂ (n * bΣ) := by
  classical
  have hterm :
      ∀ β : ((H0 ⧸ δ.ker) ⧸ M.map (QuotientGroup.mk' δ.ker)) →* ℂˣ,
        ∃ bβ : ℤ,
          quotient_pullback_pairing_linearMap δ ξH
              (((β.comp (QuotientGroup.mk' (M.map (QuotientGroup.mk' δ.ker)))).toCharacterRing -
                    1 :
                  R(H0 ⧸ δ.ker))) =
            algebraMap ℤ ℂ (n * bβ) := by
    intro β
    -- Each iterated quotient summand is already controlled individually by the strict-branch
    -- smaller-kernel package after transporting through the third-isomorphism comparison.
    exact
      strict_branch_iterated_difference_term_divisible
        (δ := δ)
        (M := M)
        hδker_lt_M
        hprime
        ξH
        hMpair
        hsmaller
        β
  -- Package the termwise transported iterated quotient witnesses into one finite-sum witness.
  exact
    strict_branch_iterated_quotient_sum_divisible_of_termwise
      (δ := δ)
      (M := M)
      (ξH := ξH)
      hterm

/-- Helper for Remark 11-11.1-3: after removing the trivial quotient character, every
nonfaithful erased quotient branch in the strict branch is already controlled by the
smaller-kernel hypothesis, so the whole residual family packages into a single `n`-multiple. -/
private theorem strict_branch_nontrivial_nonfaithful_residual_sum_divisible
    {H0 : Type*} [Group H0] [Finite H0] {n : ℤ}
    (δ : H0 →* ℂˣ)
    (ξH : R(H0))
    (hsmaller :
      ∀ ε : H0 →* ℂˣ, ε ≠ 1 → ε.ker.index < δ.ker.index →
        ∃ bC : ℤ,
          (ε.ker.index : ℂ) * ⟪((1 : R(H0)) : H0 → ℂ), (ξH : H0 → ℂ)⟫ +
            ∑ γ in
                ((Finset.univ.erase
                    (QuotientGroup.lift ε.ker ε (show ε.ker ≤ ε.ker from le_rfl))).filter
                  fun γ => γ.ker = ⊥),
                ⟪((((γ.comp (QuotientGroup.mk' ε.ker)).toCharacterRing - 1 : R(H0)) :
                      H0 → ℂ),
                    (ξH : H0 → ℂ)⟫ =
              algebraMap ℤ ℂ (n * bC)) :
    let δq : (H0 ⧸ δ.ker) →* ℂˣ :=
      QuotientGroup.lift δ.ker δ (show δ.ker ≤ δ.ker from le_rfl)
    let residualTerm : ((H0 ⧸ δ.ker) →* ℂˣ) → ℂ := fun γ ↦
      let ε : H0 →* ℂˣ := γ.comp (QuotientGroup.mk' δ.ker)
      (ε.ker.index : ℂ) * ⟪((1 : R(H0)) : H0 → ℂ), (ξH : H0 → ℂ)⟫ +
        ∑ θ in
            ((Finset.univ.erase
                (QuotientGroup.lift ε.ker ε (show ε.ker ≤ ε.ker from le_rfl))).filter
              fun θ => θ.ker = ⊥),
            ⟪((((θ.comp (QuotientGroup.mk' ε.ker)).toCharacterRing - 1 : R(H0)) :
                  H0 → ℂ),
                (ξH : H0 → ℂ)⟫
    ∃ bNF : ℤ,
      ∑ γ in (((Finset.univ.erase δq).filter fun γ => γ.ker ≠ ⊥).erase 1), residualTerm γ =
        algebraMap ℤ ℂ (n * bNF) := by
  classical
  dsimp
  let δq : (H0 ⧸ δ.ker) →* ℂˣ :=
    QuotientGroup.lift δ.ker δ (show δ.ker ≤ δ.ker from le_rfl)
  let residualTerm : ((H0 ⧸ δ.ker) →* ℂˣ) → ℂ := fun γ ↦
    let ε : H0 →* ℂˣ := γ.comp (QuotientGroup.mk' δ.ker)
    (ε.ker.index : ℂ) * ⟪((1 : R(H0)) : H0 → ℂ), (ξH : H0 → ℂ)⟫ +
      ∑ θ in
          ((Finset.univ.erase
              (QuotientGroup.lift ε.ker ε (show ε.ker ≤ ε.ker from le_rfl))).filter
            fun θ => θ.ker = ⊥),
          ⟪((((θ.comp (QuotientGroup.mk' ε.ker)).toCharacterRing - 1 : R(H0)) :
                H0 → ℂ),
              (ξH : H0 → ℂ)⟫
  have hterm :
      ∀ γ ∈ (((Finset.univ.erase δq).filter fun γ => γ.ker ≠ ⊥).erase 1),
        ∃ bγ : ℤ, residualTerm γ = algebraMap ℤ ℂ (n * bγ) := by
    intro γ hγ
    simp only [Finset.mem_erase, Finset.mem_filter, Finset.mem_univ, true_and] at hγ
    let ε : H0 →* ℂˣ := γ.comp (QuotientGroup.mk' δ.ker)
    have hε_ne : ε ≠ 1 := by
      intro hε
      apply hγ.1
      ext x
      obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective δ.ker x
      simpa [ε] using congrFun (congrArg MonoidHom.toFun hε) y
    have hε_lt : ε.ker.index < δ.ker.index := by
      -- Nonfaithful erased quotient characters strictly enlarge the ambient kernel.
      simpa [ε] using
        kernel_growth_measure_decreases_on_nonfaithful_erased_branch δ γ hγ.2
    -- The smaller-kernel owner theorem closes each nontrivial nonfaithful branch individually.
    simpa [residualTerm, ε] using hsmaller ε hε_ne hε_lt
  -- Package the termwise smaller-kernel witnesses into one finite residual sum.
  exact
    finset_sum_int_multiples
      (s := (((Finset.univ.erase δq).filter fun γ => γ.ker ≠ ⊥).erase 1))
      (f := residualTerm)
      (n := n)
      hterm

/-- Helper for Remark 11-11.1-3: in the strict-branch residual package, the exceptional erased
nonfaithful term at `γ = 1` is exactly the pullback pairing of the trivial quotient character. -/
private theorem strict_branch_trivial_nonfaithful_erased_branch_identity
    {H0 : Type*} [Group H0] [Finite H0]
    (δ : H0 →* ℂˣ)
    (ξH : R(H0)) :
    let residualTerm : ((H0 ⧸ δ.ker) →* ℂˣ) → ℂ := fun γ ↦
      let ε : H0 →* ℂˣ := γ.comp (QuotientGroup.mk' δ.ker)
      (ε.ker.index : ℂ) * ⟪((1 : R(H0)) : H0 → ℂ), (ξH : H0 → ℂ)⟫ +
        ∑ θ in
            ((Finset.univ.erase
                (QuotientGroup.lift ε.ker ε (show ε.ker ≤ ε.ker from le_rfl))).filter
              fun θ => θ.ker = ⊥),
            ⟪((((θ.comp (QuotientGroup.mk' ε.ker)).toCharacterRing - 1 : R(H0)) :
                  H0 → ℂ),
                (ξH : H0 → ℂ)⟫
    residualTerm (1 : (H0 ⧸ δ.ker) →* ℂˣ) =
      quotient_pullback_pairing_linearMap δ ξH (1 : R(H0 ⧸ δ.ker)) := by
  classical
  -- Evaluate the residual term at the trivial quotient character and collapse the now-empty
  -- erased quotient family.
  simpa [quotient_pullback_pairing_linearMap_one]

/-- Helper for Remark 11-11.1-3: in the strict branch, the full nonfaithful erased quotient
family splits at the exceptional term `γ = 1`. -/
private theorem strict_branch_nonfaithful_residual_sum_split_at_one
    {H0 : Type*} [Group H0] [Finite H0]
    (δ : H0 →* ℂˣ)
    (ξH : R(H0))
    (hδ : δ ≠ 1) :
    let δq : (H0 ⧸ δ.ker) →* ℂˣ :=
      QuotientGroup.lift δ.ker δ (show δ.ker ≤ δ.ker from le_rfl)
    let residualTerm : ((H0 ⧸ δ.ker) →* ℂˣ) → ℂ := fun γ ↦
      let ε : H0 →* ℂˣ := γ.comp (QuotientGroup.mk' δ.ker)
      (ε.ker.index : ℂ) * ⟪((1 : R(H0)) : H0 → ℂ), (ξH : H0 → ℂ)⟫ +
        ∑ θ in
            ((Finset.univ.erase
                (QuotientGroup.lift ε.ker ε (show ε.ker ≤ ε.ker from le_rfl))).filter
              fun θ => θ.ker = ⊥),
            ⟪((((θ.comp (QuotientGroup.mk' ε.ker)).toCharacterRing - 1 : R(H0)) :
                  H0 → ℂ),
                (ξH : H0 → ℂ)⟫
    ∑ γ in ((Finset.univ.erase δq).filter fun γ => γ.ker ≠ ⊥), residualTerm γ =
      residualTerm (1 : (H0 ⧸ δ.ker) →* ℂˣ) +
        ∑ γ in (((Finset.univ.erase δq).filter fun γ => γ.ker ≠ ⊥).erase 1), residualTerm γ := by
  classical
  dsimp
  have hδq_ne :
      QuotientGroup.lift δ.ker δ (show δ.ker ≤ δ.ker from le_rfl) ≠ 1 := by
    exact kernel_quotient_character_ne_one δ hδ
  have hone_mem :
      (1 : (H0 ⧸ δ.ker) →* ℂˣ) ∈
        ((Finset.univ.erase
            (QuotientGroup.lift δ.ker δ (show δ.ker ≤ δ.ker from le_rfl))).filter
          fun γ => γ.ker ≠ ⊥) := by
    simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_univ, true_and]
    refine ⟨by simpa using hδq_ne.symm, ?_⟩
    intro hker
    apply hδq_ne
    ext x
    have hxker : x ∈ (1 : (H0 ⧸ δ.ker) →* ℂˣ).ker := by
      simp [MonoidHom.mem_ker]
    have hxbot : x ∈ (⊥ : Subgroup (H0 ⧸ δ.ker)) := by
      simpa [hker] using hxker
    have hxone : x = 1 := by
      simpa using hxbot
    simpa [hxone]
  -- Isolate the exceptional erased nonfaithful term before packaging the remaining residual
  -- branch by the smaller-kernel theorem.
  simpa using
    (Finset.sum_erase_add
      (s := ((Finset.univ.erase
          (QuotientGroup.lift δ.ker δ (show δ.ker ≤ δ.ker from le_rfl))).filter
        fun γ => γ.ker ≠ ⊥))
      (a := (1 : (H0 ⧸ δ.ker) →* ℂˣ))
      hone_mem).symm

/-- Helper for Remark 11-11.1-3: once the exceptional term `γ = 1` is separated, the whole
nonfaithful erased quotient branch is the trivial quotient-character contribution plus one
packaged `n`-multiple. -/
private theorem strict_branch_full_nonfaithful_residual_sum_eq_trivial_plus_divisible
    {H0 : Type*} [Group H0] [Finite H0] {n : ℤ}
    (δ : H0 →* ℂˣ)
    (M : Subgroup H0) [M.Normal]
    (hδker_lt_M : δ.ker < M)
    (ξH : R(H0))
    (hsmaller :
      ∀ ε : H0 →* ℂˣ, ε ≠ 1 → ε.ker.index < δ.ker.index →
        ∃ bC : ℤ,
          (ε.ker.index : ℂ) * ⟪((1 : R(H0)) : H0 → ℂ), (ξH : H0 → ℂ)⟫ +
            ∑ γ in
                ((Finset.univ.erase
                    (QuotientGroup.lift ε.ker ε (show ε.ker ≤ ε.ker from le_rfl))).filter
                  fun γ => γ.ker = ⊥),
                ⟪((((γ.comp (QuotientGroup.mk' ε.ker)).toCharacterRing - 1 : R(H0)) :
                      H0 → ℂ),
                    (ξH : H0 → ℂ)⟫ =
              algebraMap ℤ ℂ (n * bC)) :
    let δq : (H0 ⧸ δ.ker) →* ℂˣ :=
      QuotientGroup.lift δ.ker δ (show δ.ker ≤ δ.ker from le_rfl)
    let residualTerm : ((H0 ⧸ δ.ker) →* ℂˣ) → ℂ := fun γ ↦
      let ε : H0 →* ℂˣ := γ.comp (QuotientGroup.mk' δ.ker)
      (ε.ker.index : ℂ) * ⟪((1 : R(H0)) : H0 → ℂ), (ξH : H0 → ℂ)⟫ +
        ∑ θ in
            ((Finset.univ.erase
                (QuotientGroup.lift ε.ker ε (show ε.ker ≤ ε.ker from le_rfl))).filter
              fun θ => θ.ker = ⊥),
            ⟪((((θ.comp (QuotientGroup.mk' ε.ker)).toCharacterRing - 1 : R(H0)) :
                  H0 → ℂ),
                (ξH : H0 → ℂ)⟫
    ∃ bNF : ℤ,
      ∑ γ in ((Finset.univ.erase δq).filter fun γ => γ.ker ≠ ⊥), residualTerm γ =
        quotient_pullback_pairing_linearMap δ ξH (1 : R(H0 ⧸ δ.ker)) +
          algebraMap ℤ ℂ (n * bNF) := by
  classical
  dsimp
  have hδ : δ ≠ 1 := by
    intro hδ
    have hker_top : δ.ker = ⊤ := by
      ext x
      simp [hδ, MonoidHom.mem_ker]
    have hnot_lt : ¬ δ.ker < M := by
      simpa [hker_top] using (show ¬ (⊤ : Subgroup H0) < M from not_lt_of_ge le_top)
    exact hnot_lt hδker_lt_M
  have hsplit :
      ∑ γ in ((Finset.univ.erase
          (QuotientGroup.lift δ.ker δ (show δ.ker ≤ δ.ker from le_rfl))).filter
        fun γ => γ.ker ≠ ⊥),
          residualTerm γ =
        residualTerm (1 : (H0 ⧸ δ.ker) →* ℂˣ) +
          ∑ γ in
              (((Finset.univ.erase
                  (QuotientGroup.lift δ.ker δ (show δ.ker ≤ δ.ker from le_rfl))).filter
                fun γ => γ.ker ≠ ⊥).erase 1),
              residualTerm γ := by
    -- Separate the exceptional erased nonfaithful branch before applying the packaged
    -- smaller-kernel arithmetic.
    simpa using
      strict_branch_nonfaithful_residual_sum_split_at_one
        (δ := δ)
        (ξH := ξH)
        hδ
  have htrivial :
      residualTerm (1 : (H0 ⧸ δ.ker) →* ℂˣ) =
        quotient_pullback_pairing_linearMap δ ξH (1 : R(H0 ⧸ δ.ker)) := by
    -- The exceptional branch is exactly the trivial quotient-character contribution.
    simpa using
      strict_branch_trivial_nonfaithful_erased_branch_identity
        (δ := δ)
        (ξH := ξH)
  have hnontrivial :
      ∃ bNF : ℤ,
        ∑ γ in
            (((Finset.univ.erase
                (QuotientGroup.lift δ.ker δ (show δ.ker ≤ δ.ker from le_rfl))).filter
              fun γ => γ.ker ≠ ⊥).erase 1),
            residualTerm γ =
          algebraMap ℤ ℂ (n * bNF) := by
    -- All remaining erased nonfaithful branches are genuinely smaller-kernel cases.
    simpa using
      strict_branch_nontrivial_nonfaithful_residual_sum_divisible
        (δ := δ)
        (ξH := ξH)
        hsmaller
  rcases hnontrivial with ⟨bNF, hbNF⟩
  refine ⟨bNF, ?_⟩
  -- Reassemble the full nonfaithful branch from the exceptional term and the packaged remainder.
  calc
    ∑ γ in ((Finset.univ.erase
        (QuotientGroup.lift δ.ker δ (show δ.ker ≤ δ.ker from le_rfl))).filter
      fun γ => γ.ker ≠ ⊥),
        residualTerm γ =
      residualTerm (1 : (H0 ⧸ δ.ker) →* ℂˣ) +
        ∑ γ in
            (((Finset.univ.erase
                (QuotientGroup.lift δ.ker δ (show δ.ker ≤ δ.ker from le_rfl))).filter
              fun γ => γ.ker ≠ ⊥).erase 1),
            residualTerm γ := hsplit
    _ =
      quotient_pullback_pairing_linearMap δ ξH (1 : R(H0 ⧸ δ.ker)) +
        algebraMap ℤ ℂ (n * bNF) := by
          rw [htrivial, hbNF]

/-- Helper for Remark 11-11.1-3: after moving the exceptional `γ = 1` branch to the right, the
remaining strict-branch nonfaithful residual is already a pure `n`-multiple. -/
private theorem strict_branch_full_nonfaithful_residual_minus_trivial_divisible
    {H0 : Type*} [Group H0] [Finite H0] {n : ℤ}
    (δ : H0 →* ℂˣ)
    (M : Subgroup H0) [M.Normal]
    (hδker_lt_M : δ.ker < M)
    (ξH : R(H0))
    (hsmaller :
      ∀ ε : H0 →* ℂˣ, ε ≠ 1 → ε.ker.index < δ.ker.index →
        ∃ bC : ℤ,
          (ε.ker.index : ℂ) * ⟪((1 : R(H0)) : H0 → ℂ), (ξH : H0 → ℂ)⟫ +
            ∑ γ in
                ((Finset.univ.erase
                    (QuotientGroup.lift ε.ker ε (show ε.ker ≤ ε.ker from le_rfl))).filter
                  fun γ => γ.ker = ⊥),
                ⟪((((γ.comp (QuotientGroup.mk' ε.ker)).toCharacterRing - 1 : R(H0)) :
                      H0 → ℂ),
                    (ξH : H0 → ℂ)⟫ =
              algebraMap ℤ ℂ (n * bC)) :
    let δq : (H0 ⧸ δ.ker) →* ℂˣ :=
      QuotientGroup.lift δ.ker δ (show δ.ker ≤ δ.ker from le_rfl)
    let residualTerm : ((H0 ⧸ δ.ker) →* ℂˣ) → ℂ := fun γ ↦
      let ε : H0 →* ℂˣ := γ.comp (QuotientGroup.mk' δ.ker)
      (ε.ker.index : ℂ) * ⟪((1 : R(H0)) : H0 → ℂ), (ξH : H0 → ℂ)⟫ +
        ∑ θ in
            ((Finset.univ.erase
                (QuotientGroup.lift ε.ker ε (show ε.ker ≤ ε.ker from le_rfl))).filter
              fun θ => θ.ker = ⊥),
            ⟪((((θ.comp (QuotientGroup.mk' ε.ker)).toCharacterRing - 1 : R(H0)) :
                  H0 → ℂ),
                (ξH : H0 → ℂ)⟫
    ∃ bNF : ℤ,
      (∑ γ in ((Finset.univ.erase δq).filter fun γ => γ.ker ≠ ⊥), residualTerm γ) -
          quotient_pullback_pairing_linearMap δ ξH (1 : R(H0 ⧸ δ.ker)) =
        algebraMap ℤ ℂ (n * bNF) := by
  classical
  dsimp
  rcases
      strict_branch_full_nonfaithful_residual_sum_eq_trivial_plus_divisible
        (δ := δ)
        (M := M)
        hδker_lt_M
        (ξH := ξH)
        hsmaller with
    ⟨bNF, hbNF⟩
  refine ⟨bNF, ?_⟩
  -- Subtract the exceptional trivial branch from the packaged full nonfaithful sum.
  calc
    (∑ γ in ((Finset.univ.erase
        (QuotientGroup.lift δ.ker δ (show δ.ker ≤ δ.ker from le_rfl))).filter
      fun γ => γ.ker ≠ ⊥),
        residualTerm γ) -
        quotient_pullback_pairing_linearMap δ ξH (1 : R(H0 ⧸ δ.ker)) =
      (quotient_pullback_pairing_linearMap δ ξH (1 : R(H0 ⧸ δ.ker)) +
          algebraMap ℤ ℂ (n * bNF)) -
        quotient_pullback_pairing_linearMap δ ξH (1 : R(H0 ⧸ δ.ker)) := by
          rw [hbNF]
    _ = algebraMap ℤ ℂ (n * bNF) := by
          abel

/-- Helper for Remark 11-11.1-3: each strict-branch residual summand is the faithful quotient
top-layer pairing for the smaller-kernel ambient character obtained by pulling `γ` back to `H0`.
-/
private theorem strict_branch_nonfaithful_residual_term_as_smaller_top_layer
    {H0 : Type*} [Group H0] [Finite H0]
    (δ : H0 →* ℂˣ)
    (ξH : R(H0))
    (γ : (H0 ⧸ δ.ker) →* ℂˣ) :
    let ε : H0 →* ℂˣ := γ.comp (QuotientGroup.mk' δ.ker)
    let residualTerm : ((H0 ⧸ δ.ker) →* ℂˣ) → ℂ := fun γ ↦
      let ε : H0 →* ℂˣ := γ.comp (QuotientGroup.mk' δ.ker)
      (ε.ker.index : ℂ) * ⟪((1 : R(H0)) : H0 → ℂ), (ξH : H0 → ℂ)⟫ +
        ∑ θ in
            ((Finset.univ.erase
                (QuotientGroup.lift ε.ker ε (show ε.ker ≤ ε.ker from le_rfl))).filter
              fun θ => θ.ker = ⊥),
            ⟪((((θ.comp (QuotientGroup.mk' ε.ker)).toCharacterRing - 1 : R(H0)) :
                  H0 → ℂ),
                (ξH : H0 → ℂ)⟫
    let ηε : R(H0 ⧸ ε.ker) :=
      (ε.ker.index : ℤ) • (1 : R(H0 ⧸ ε.ker)) +
        ∑ θ in
            ((Finset.univ.erase
                (QuotientGroup.lift ε.ker ε (show ε.ker ≤ ε.ker from le_rfl))).filter
              fun θ => θ.ker = ⊥),
            ((θ.toCharacterRing - 1 : R(H0 ⧸ ε.ker)))
    residualTerm γ = quotient_pullback_pairing_linearMap ε ξH ηε := by
  classical
  dsimp
  -- Rewrite the residual scalar directly as the smaller-kernel faithful top layer.
  simpa using faithful_quotient_top_layer_eq_quotient_pullback_pairing (β := ε) (ξ := ξH)

/-- Helper for Remark 11-11.1-3: the mapped-coatom correction term `ηM` already reduces to the
index-scaled trivial line after applying the quotient pullback pairing. -/
private theorem strict_branch_etaM_pairing_eq_mapped_coatom_index_trivial
    {H0 : Type*} [Group H0] [Finite H0]
    (δ : H0 →* ℂˣ)
    (M : Subgroup H0) [M.Normal]
    (hδker_lt_M : δ.ker < M)
    (ξH : R(H0)) :
    let Mq : Subgroup (H0 ⧸ δ.ker) := M.map (QuotientGroup.mk' δ.ker)
    let ηM : R(H0 ⧸ δ.ker) :=
      Subgroup.characterRingInduction Mq (1 : R(Mq)) -
        ∑ β : ((H0 ⧸ δ.ker) ⧸ Mq) →* ℂˣ,
          (((β.comp (QuotientGroup.mk' Mq)).toCharacterRing - 1 : R(H0 ⧸ δ.ker)))
    quotient_pullback_pairing_linearMap δ ξH ηM =
      (M.index : ℂ) * quotient_pullback_pairing_linearMap δ ξH (1 : R(H0 ⧸ δ.ker)) := by
  classical
  dsimp
  let e : H0 ⧸ δ.ker ≃* δ.range := QuotientGroup.quotientKerEquivRange δ
  have hcomm_quot : ∀ a b : H0 ⧸ δ.ker, a * b = b * a := by
    intro a b
    -- The quotient by `δ.ker` identifies with a subgroup of the commutative group `ℂˣ`.
    apply e.injective
    simp [mul_comm]
  letI : CommGroup (H0 ⧸ δ.ker) :=
    { QuotientGroup.Quotient.group δ.ker with
      mul_comm := hcomm_quot }
  let Mq : Subgroup (H0 ⧸ δ.ker) := M.map (QuotientGroup.mk' δ.ker)
  letI : Fintype (((H0 ⧸ δ.ker) ⧸ Mq) →* ℂˣ) := linearCharacterFintype
  have hMq_index : Mq.index = M.index := by
    -- Replace the mapped-coatom index by the direct quotient index of `M`.
    rw [Mq.index_eq_card, M.index_eq_card]
    simpa [Mq] using quotient_map_card_eq_quotient_card δ.ker M hδker_lt_M.le
  have hrewrite :
      quotient_pullback_pairing_linearMap δ ξH
          (Subgroup.characterRingInduction Mq (1 : R(Mq))) =
        (Mq.index : ℂ) * quotient_pullback_pairing_linearMap δ ξH (1 : R(H0 ⧸ δ.ker)) +
          ∑ β : ((H0 ⧸ δ.ker) ⧸ Mq) →* ℂˣ,
            quotient_pullback_pairing_linearMap δ ξH
              (((β.comp (QuotientGroup.mk' Mq)).toCharacterRing - 1 : R(H0 ⧸ δ.ker))) := by
    -- Expand the mapped-coatom induced-trivial term into its trivial-line part and the full
    -- iterated quotient-character difference family.
    simpa [Mq] using
      quotient_pullback_pairing_induced_trivial_eq_index_trivial_add_difference_sum
        (β := δ)
        (ξ := ξH)
        (M := Mq)
        (fun a b ↦ by simpa using (mul_comm a b))
  calc
    quotient_pullback_pairing_linearMap δ ξH
        (Subgroup.characterRingInduction Mq (1 : R(Mq)) -
          ∑ β : ((H0 ⧸ δ.ker) ⧸ Mq) →* ℂˣ,
            (((β.comp (QuotientGroup.mk' Mq)).toCharacterRing - 1 : R(H0 ⧸ δ.ker)))) =
      quotient_pullback_pairing_linearMap δ ξH
          (Subgroup.characterRingInduction Mq (1 : R(Mq))) -
        ∑ β : ((H0 ⧸ δ.ker) ⧸ Mq) →* ℂˣ,
          quotient_pullback_pairing_linearMap δ ξH
            (((β.comp (QuotientGroup.mk' Mq)).toCharacterRing - 1 : R(H0 ⧸ δ.ker))) := by
          simp
    _ =
      (Mq.index : ℂ) * quotient_pullback_pairing_linearMap δ ξH (1 : R(H0 ⧸ δ.ker)) := by
        rw [hrewrite]
        abel
    _ =
      (M.index : ℂ) * quotient_pullback_pairing_linearMap δ ξH (1 : R(H0 ⧸ δ.ker)) := by
        rw [hMq_index]

/-- Helper for Remark 11-11.1-3: transporting the mapped-coatom iterated quotient family through
Noether's third isomorphism identifies it exactly with the faithful prime-quotient difference
family on `H0 ⧸ M`. -/
private theorem strict_branch_iterated_difference_sum_eq_prime_quotient_faithful_sum
    {H0 : Type*} [Group H0] [Finite H0]
    (δ : H0 →* ℂˣ)
    (M : Subgroup H0) [M.Normal]
    (hδker_lt_M : δ.ker < M)
    (hprime : (Nat.card (H0 ⧸ M)).Prime)
    (ξH : R(H0)) :
    let Mq : Subgroup (H0 ⧸ δ.ker) := M.map (QuotientGroup.mk' δ.ker)
    ∑ β : ((H0 ⧸ δ.ker) ⧸ Mq) →* ℂˣ,
      quotient_pullback_pairing_linearMap δ ξH
        (((β.comp (QuotientGroup.mk' Mq)).toCharacterRing - 1 : R(H0 ⧸ δ.ker))) =
      ∑ β in ((Finset.univ.erase (1 : (H0 ⧸ M) →* ℂˣ)).filter fun β => β.ker = ⊥),
        ⟪((((β.comp (QuotientGroup.mk' M)).toCharacterRing - 1 : R(H0)) : H0 → ℂ),
            (ξH : H0 → ℂ)⟫ := by
  classical
  dsimp
  let e : ((H0 ⧸ δ.ker) ⧸ M.map (QuotientGroup.mk' δ.ker)) ≃* H0 ⧸ M :=
    QuotientGroup.quotientQuotientEquivQuotient δ.ker M hδker_lt_M.le
  let eχ :
      ((H0 ⧸ M) →* ℂˣ) ≃
        (((H0 ⧸ δ.ker) ⧸ M.map (QuotientGroup.mk' δ.ker)) →* ℂˣ) where
    toFun := fun β ↦ β.comp e.toMonoidHom
    invFun := fun β ↦ β.comp e.symm.toMonoidHom
    left_inv := by
      intro β
      ext x
      rfl
    right_inv := by
      intro β
      ext x
      rfl
  let iterTerm :
      (((H0 ⧸ δ.ker) ⧸ M.map (QuotientGroup.mk' δ.ker)) →* ℂˣ) → ℂ := fun β ↦
        quotient_pullback_pairing_linearMap δ ξH
          (((β.comp (QuotientGroup.mk' (M.map (QuotientGroup.mk' δ.ker)))).toCharacterRing - 1 :
              R(H0 ⧸ δ.ker)))
  let directTerm : ((H0 ⧸ M) →* ℂˣ) → ℂ := fun β ↦
    ⟪((((β.comp (QuotientGroup.mk' M)).toCharacterRing - 1 : R(H0)) : H0 → ℂ),
        (ξH : H0 → ℂ)⟫
  have htransport :
      ∀ β : (H0 ⧸ M) →* ℂˣ,
        iterTerm (eχ β) = directTerm β := by
    intro β
    -- Transport each iterated quotient summand through the third-isomorphism equivalence so it
    -- becomes exactly the ambient prime-quotient lift summand.
    simpa [iterTerm, directTerm, eχ, e] using
      quotient_pullback_pairing_linearMap_difference_via_third_iso
        (δ := δ)
        (M := M)
        hδker_lt_M.le
        ξH
        (β.comp e.toMonoidHom)
  have hsum_transport :
      ∑ β : ((H0 ⧸ δ.ker) ⧸ M.map (QuotientGroup.mk' δ.ker)) →* ℂˣ, iterTerm β =
        ∑ β : (H0 ⧸ M) →* ℂˣ, directTerm β := by
    -- Reindex the iterated quotient character family by the third-isomorphism equivalence.
    exact Fintype.sum_equiv eχ directTerm iterTerm htransport
  have hsplit :
      ∑ β : (H0 ⧸ M) →* ℂˣ, directTerm β =
        directTerm (1 : (H0 ⧸ M) →* ℂˣ) +
          ∑ β in Finset.univ.erase (1 : (H0 ⧸ M) →* ℂˣ), directTerm β := by
    -- Isolate the trivial quotient character so the remaining family matches the faithful branch.
    simpa [directTerm] using
      (Finset.sum_erase_add
        (s := Finset.univ)
        (a := (1 : (H0 ⧸ M) →* ℂˣ))
        (by simp)).symm
  have hone :
      directTerm (1 : (H0 ⧸ M) →* ℂˣ) = 0 := by
    -- The trivial quotient character contributes the zero difference term.
    simp [directTerm]
  calc
    ∑ β : ((H0 ⧸ δ.ker) ⧸ M.map (QuotientGroup.mk' δ.ker)) →* ℂˣ, iterTerm β =
        ∑ β : (H0 ⧸ M) →* ℂˣ, directTerm β := hsum_transport
    _ =
        directTerm (1 : (H0 ⧸ M) →* ℂˣ) +
          ∑ β in Finset.univ.erase (1 : (H0 ⧸ M) →* ℂˣ), directTerm β := hsplit
    _ =
        ∑ β in Finset.univ.erase (1 : (H0 ⧸ M) →* ℂˣ), directTerm β := by
          rw [hone]
          simp
    _ =
        ∑ β in ((Finset.univ.erase (1 : (H0 ⧸ M) →* ℂˣ)).filter fun β => β.ker = ⊥),
          directTerm β := by
            symm
            simpa [prime_quotient_faithful_filter_eq_erase_one (M := M) hprime]

/-- Helper for Remark 11-11.1-3: splitting an erased quotient-character family by kernel type
records the faithful and nonfaithful branches separately. -/
private theorem strict_branch_erased_sum_split_by_kernel_type
    {Q : Type*} [Group Q] [Finite Q]
    (δq : Q →* ℂˣ)
    (ambientTerm : (Q →* ℂˣ) → ℂ) :
    ∑ γ in Finset.univ.erase δq, ambientTerm γ =
      ∑ γ in ((Finset.univ.erase δq).filter fun γ => γ.ker = ⊥), ambientTerm γ +
        ∑ γ in ((Finset.univ.erase δq).filter fun γ => γ.ker ≠ ⊥), ambientTerm γ := by
  classical
  -- Split the erased quotient-character family once into faithful and nonfaithful branches.
  simpa using
    (Finset.sum_filter_add_sum_filter_not
      (s := Finset.univ.erase δq)
      (f := ambientTerm)
      (p := fun γ : Q →* ℂˣ => γ.ker = ⊥)).symm

/-- Helper for Remark 11-11.1-3: after normalizing the mapped-coatom block, the strict branch is
reduced to one additive partition between the faithful erased branches and the nonfaithful
residual branches at the chosen coatom. -/
private theorem strict_branch_nonfaithful_branch_partition_at_mapped_coatom
    {H0 : Type*} [Group H0] [Finite H0]
    (δ : H0 →* ℂˣ)
    (M : Subgroup H0) [M.Normal]
    (_hδker_lt_M : δ.ker < M)
    (_hprime : (Nat.card (H0 ⧸ M)).Prime)
    (ξH : R(H0)) :
    let δq : (H0 ⧸ δ.ker) →* ℂˣ :=
      QuotientGroup.lift δ.ker δ (show δ.ker ≤ δ.ker from le_rfl)
    let qpp1 : ℂ :=
      quotient_pullback_pairing_linearMap δ ξH (1 : R(H0 ⧸ δ.ker))
    let ambientTerm : ((H0 ⧸ δ.ker) →* ℂˣ) → ℂ := fun γ ↦
      ⟪((((γ.comp (QuotientGroup.mk' δ.ker)).toCharacterRing - 1 : R(H0)) : H0 → ℂ),
          (ξH : H0 → ℂ)⟫
    let residualTerm : ((H0 ⧸ δ.ker) →* ℂˣ) → ℂ := fun γ ↦
      let ε : H0 →* ℂˣ := γ.comp (QuotientGroup.mk' δ.ker)
      (ε.ker.index : ℂ) * ⟪((1 : R(H0)) : H0 → ℂ), (ξH : H0 → ℂ)⟫ +
        ∑ θ in
            ((Finset.univ.erase
                (QuotientGroup.lift ε.ker ε (show ε.ker ≤ ε.ker from le_rfl))).filter
              fun θ => θ.ker = ⊥),
            ⟪((((θ.comp (QuotientGroup.mk' ε.ker)).toCharacterRing - 1 : R(H0)) :
                  H0 → ℂ),
                (ξH : H0 → ℂ)⟫
    (M.index : ℂ) * qpp1 +
        ∑ γ in ((Finset.univ.erase δq).filter fun γ => γ.ker ≠ ⊥), residualTerm γ =
      (δ.ker.index : ℂ) * qpp1 +
        ∑ γ in ((Finset.univ.erase δq).filter fun γ => γ.ker = ⊥), ambientTerm γ +
          qpp1 := by
  classical
  dsimp
  set qpp1 : ℂ :=
    quotient_pullback_pairing_linearMap δ ξH (1 : R(H0 ⧸ δ.ker))
  set ambientTerm : ((H0 ⧸ δ.ker) →* ℂˣ) → ℂ := fun γ ↦
    ⟪((((γ.comp (QuotientGroup.mk' δ.ker)).toCharacterRing - 1 : R(H0)) : H0 → ℂ),
        (ξH : H0 → ℂ)⟫
  set residualTerm : ((H0 ⧸ δ.ker) →* ℂˣ) → ℂ := fun γ ↦
    let ε : H0 →* ℂˣ := γ.comp (QuotientGroup.mk' δ.ker)
    (ε.ker.index : ℂ) * ⟪((1 : R(H0)) : H0 → ℂ), (ξH : H0 → ℂ)⟫ +
      ∑ θ in
          ((Finset.univ.erase
              (QuotientGroup.lift ε.ker ε (show ε.ker ≤ ε.ker from le_rfl))).filter
            fun θ => θ.ker = ⊥),
          ⟪((((θ.comp (QuotientGroup.mk' ε.ker)).toCharacterRing - 1 : R(H0)) :
                H0 → ℂ),
              (ξH : H0 → ℂ)⟫
  have hsum_split :
      ∑ γ in Finset.univ.erase
          (QuotientGroup.lift δ.ker δ (show δ.ker ≤ δ.ker from le_rfl)),
          ambientTerm γ =
        ∑ γ in
            ((Finset.univ.erase
                (QuotientGroup.lift δ.ker δ (show δ.ker ≤ δ.ker from le_rfl))).filter
              fun γ => γ.ker = ⊥),
            ambientTerm γ +
          ∑ γ in
            ((Finset.univ.erase
                (QuotientGroup.lift δ.ker δ (show δ.ker ≤ δ.ker from le_rfl))).filter
              fun γ => γ.ker ≠ ⊥),
            ambientTerm γ := by
    -- Keep the faithful/nonfaithful partition explicit before inserting the mapped-coatom block.
    simpa [ambientTerm] using
      strict_branch_erased_sum_split_by_kernel_type
        (δq := QuotientGroup.lift δ.ker δ (show δ.ker ≤ δ.ker from le_rfl))
        ambientTerm
  -- Route correction: the transport and smaller-kernel rewrites are already normalized earlier.
  -- TODO: combine `hsum_split` with the mapped-coatom decomposition, rewrite the faithful branch
  -- via the transported iterated quotient sum, rewrite each nonfaithful summand via the smaller-
  -- kernel top layer, and then isolate the exceptional trivial branch `γ = 1`.
  sorry

/-- Helper for Remark 11-11.1-3: the strict-branch frontier is the additive source-faithful
partition identity, with the mapped-coatom block and the nonfaithful residual family on the left
and the original top layer plus the exceptional trivial branch on the right. -/
private theorem strict_branch_top_layer_plus_trivial_eq_mapped_block_plus_nonfaithful_residual
    {H0 : Type*} [Group H0] [Finite H0]
    (δ : H0 →* ℂˣ)
    (M : Subgroup H0) [M.Normal]
    (hδker_lt_M : δ.ker < M)
    (hprime : (Nat.card (H0 ⧸ M)).Prime)
    (ξH : R(H0)) :
    let Mq : Subgroup (H0 ⧸ δ.ker) := M.map (QuotientGroup.mk' δ.ker)
    let δq : (H0 ⧸ δ.ker) →* ℂˣ :=
      QuotientGroup.lift δ.ker δ (show δ.ker ≤ δ.ker from le_rfl)
    let η : R(H0 ⧸ δ.ker) :=
      (δ.ker.index : ℤ) • (1 : R(H0 ⧸ δ.ker)) +
        ∑ γ in ((Finset.univ.erase δq).filter fun γ => γ.ker = ⊥),
          ((γ.toCharacterRing - 1 : R(H0 ⧸ δ.ker)))
    let ηM : R(H0 ⧸ δ.ker) :=
      Subgroup.characterRingInduction Mq (1 : R(Mq)) -
        ∑ β : ((H0 ⧸ δ.ker) ⧸ Mq) →* ℂˣ,
          (((β.comp (QuotientGroup.mk' Mq)).toCharacterRing - 1 : R(H0 ⧸ δ.ker)))
    let residualTerm : ((H0 ⧸ δ.ker) →* ℂˣ) → ℂ := fun γ ↦
      let ε : H0 →* ℂˣ := γ.comp (QuotientGroup.mk' δ.ker)
      (ε.ker.index : ℂ) * ⟪((1 : R(H0)) : H0 → ℂ), (ξH : H0 → ℂ)⟫ +
        ∑ θ in
            ((Finset.univ.erase
                (QuotientGroup.lift ε.ker ε (show ε.ker ≤ ε.ker from le_rfl))).filter
              fun θ => θ.ker = ⊥),
            ⟪((((θ.comp (QuotientGroup.mk' ε.ker)).toCharacterRing - 1 : R(H0)) :
                  H0 → ℂ),
                (ξH : H0 → ℂ)⟫
    quotient_pullback_pairing_linearMap δ ξH ηM +
        ∑ γ in ((Finset.univ.erase δq).filter fun γ => γ.ker ≠ ⊥), residualTerm γ =
      quotient_pullback_pairing_linearMap δ ξH η +
        quotient_pullback_pairing_linearMap δ ξH (1 : R(H0 ⧸ δ.ker)) := by
  classical
  dsimp
  set qpp1 : ℂ :=
    quotient_pullback_pairing_linearMap δ ξH (1 : R(H0 ⧸ δ.ker))
  set ambientTerm : ((H0 ⧸ δ.ker) →* ℂˣ) → ℂ := fun γ ↦
    ⟪((((γ.comp (QuotientGroup.mk' δ.ker)).toCharacterRing - 1 : R(H0)) : H0 → ℂ),
        (ξH : H0 → ℂ)⟫
  have htop_layer :
      quotient_pullback_pairing_linearMap δ ξH η =
        (δ.ker.index : ℂ) * qpp1 +
          ∑ γ in
              ((Finset.univ.erase
                  (QuotientGroup.lift δ.ker δ (show δ.ker ≤ δ.ker from le_rfl))).filter
                fun γ => γ.ker = ⊥),
              ambientTerm γ := by
    -- Keep the faithful top layer in its explicit split form before matching the strict branches.
    simpa [qpp1, ambientTerm] using
      faithful_quotient_top_layer_eq_quotient_pullback_pairing (β := δ) (ξ := ξH)
  have hηM :
      quotient_pullback_pairing_linearMap δ ξH ηM = (M.index : ℂ) * qpp1 := by
    -- Normalize the mapped-coatom correction term to the index-scaled trivial line.
    simpa [qpp1, ηM] using
      strict_branch_etaM_pairing_eq_mapped_coatom_index_trivial
        (δ := δ)
        (M := M)
        hδker_lt_M
        (ξH := ξH)
  have hpartition :
      (M.index : ℂ) * qpp1 +
          ∑ γ in
              ((Finset.univ.erase
                  (QuotientGroup.lift δ.ker δ (show δ.ker ≤ δ.ker from le_rfl))).filter
                fun γ => γ.ker ≠ ⊥),
              residualTerm γ =
        (δ.ker.index : ℂ) * qpp1 +
          ∑ γ in
              ((Finset.univ.erase
                  (QuotientGroup.lift δ.ker δ (show δ.ker ≤ δ.ker from le_rfl))).filter
                fun γ => γ.ker = ⊥),
              ambientTerm γ +
            qpp1 := by
    -- Reduce the published theorem to the normalized branch partition at the chosen coatom.
    simpa [qpp1, ambientTerm, residualTerm] using
      strict_branch_nonfaithful_branch_partition_at_mapped_coatom
        (δ := δ)
        (M := M)
        hδker_lt_M
        hprime
        (ξH := ξH)
  -- Once the two visible normalizations are in place, the main theorem is a short wrapper.
  calc
    quotient_pullback_pairing_linearMap δ ξH ηM +
        ∑ γ in
            ((Finset.univ.erase
                (QuotientGroup.lift δ.ker δ (show δ.ker ≤ δ.ker from le_rfl))).filter
              fun γ => γ.ker ≠ ⊥),
            residualTerm γ =
      (M.index : ℂ) * qpp1 +
        ∑ γ in
            ((Finset.univ.erase
                (QuotientGroup.lift δ.ker δ (show δ.ker ≤ δ.ker from le_rfl))).filter
              fun γ => γ.ker ≠ ⊥),
            residualTerm γ := by
              rw [hηM]
    _ =
      (δ.ker.index : ℂ) * qpp1 +
        ∑ γ in
            ((Finset.univ.erase
                (QuotientGroup.lift δ.ker δ (show δ.ker ≤ δ.ker from le_rfl))).filter
              fun γ => γ.ker = ⊥),
            ambientTerm γ +
          qpp1 := hpartition
    _ =
      quotient_pullback_pairing_linearMap δ ξH η +
        quotient_pullback_pairing_linearMap δ ξH (1 : R(H0 ⧸ δ.ker)) := by
          simpa [qpp1, add_assoc, add_left_comm, add_comm] using htop_layer.symm

/-- Helper for Remark 11-11.1-3: the only unresolved strict-branch step is the pairing-level
split that rewrites the full faithful quotient top layer as the mapped-coatom block plus the
nonfaithful residual with the trivial quotient character removed once. -/
private theorem strict_branch_top_layer_pairing_minus_mapped_block_eq_nonfaithful_residual_minus_trivial
    {H0 : Type*} [Group H0] [Finite H0]
    (δ : H0 →* ℂˣ)
    (M : Subgroup H0) [M.Normal]
    (hδker_lt_M : δ.ker < M)
    (hprime : (Nat.card (H0 ⧸ M)).Prime)
    (ξH : R(H0)) :
    let Mq : Subgroup (H0 ⧸ δ.ker) := M.map (QuotientGroup.mk' δ.ker)
    let δq : (H0 ⧸ δ.ker) →* ℂˣ :=
      QuotientGroup.lift δ.ker δ (show δ.ker ≤ δ.ker from le_rfl)
    let η : R(H0 ⧸ δ.ker) :=
      (δ.ker.index : ℤ) • (1 : R(H0 ⧸ δ.ker)) +
        ∑ γ in ((Finset.univ.erase δq).filter fun γ => γ.ker = ⊥),
          ((γ.toCharacterRing - 1 : R(H0 ⧸ δ.ker)))
    let ηM : R(H0 ⧸ δ.ker) :=
      Subgroup.characterRingInduction Mq (1 : R(Mq)) -
        ∑ β : ((H0 ⧸ δ.ker) ⧸ Mq) →* ℂˣ,
          (((β.comp (QuotientGroup.mk' Mq)).toCharacterRing - 1 : R(H0 ⧸ δ.ker)))
    let residualTerm : ((H0 ⧸ δ.ker) →* ℂˣ) → ℂ := fun γ ↦
      let ε : H0 →* ℂˣ := γ.comp (QuotientGroup.mk' δ.ker)
      (ε.ker.index : ℂ) * ⟪((1 : R(H0)) : H0 → ℂ), (ξH : H0 → ℂ)⟫ +
        ∑ θ in
            ((Finset.univ.erase
                (QuotientGroup.lift ε.ker ε (show ε.ker ≤ ε.ker from le_rfl))).filter
              fun θ => θ.ker = ⊥),
            ⟪((((θ.comp (QuotientGroup.mk' ε.ker)).toCharacterRing - 1 : R(H0)) :
                  H0 → ℂ),
                (ξH : H0 → ℂ)⟫
    quotient_pullback_pairing_linearMap δ ξH η =
      quotient_pullback_pairing_linearMap δ ξH ηM +
        ((∑ γ in ((Finset.univ.erase δq).filter fun γ => γ.ker ≠ ⊥), residualTerm γ) -
          quotient_pullback_pairing_linearMap δ ξH (1 : R(H0 ⧸ δ.ker))) := by
  classical
  dsimp
  have hplus :
      quotient_pullback_pairing_linearMap δ ξH ηM +
          ∑ γ in ((Finset.univ.erase δq).filter fun γ => γ.ker ≠ ⊥), residualTerm γ =
        quotient_pullback_pairing_linearMap δ ξH η +
          quotient_pullback_pairing_linearMap δ ξH (1 : R(H0 ⧸ δ.ker)) := by
    -- The subtraction form is now reduced to the additive branch-partition identity.
    simpa [Mq, δq, η, ηM, residualTerm] using
      strict_branch_top_layer_plus_trivial_eq_mapped_block_plus_nonfaithful_residual
        (δ := δ)
        (M := M)
        hδker_lt_M
        hprime
        (ξH := ξH)
  -- Move the exceptional trivial term back to the right to recover the published minus form.
  exact eq_sub_iff_add_eq.mpr <| by
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hplus.symm

/-- Helper for Remark 11-11.1-3: once the smaller-kernel package is supplied explicitly, the
remaining strict-branch gap is a pairing-level residual decomposition from the full faithful
quotient top layer to the mapped-coatom block. -/
private theorem strict_branch_faithful_top_layer_pairing_eq_mapped_block_plus_divisible_residual
    {H0 : Type*} [Group H0] [Finite H0] {n : ℤ}
    (δ : H0 →* ℂˣ)
    (M : Subgroup H0) [M.Normal]
    (hδker_lt_M : δ.ker < M)
    (hprime : (Nat.card (H0 ⧸ M)).Prime)
    (ξH : R(H0))
    (hMpair :
      ∃ bM : ℤ,
        ⟪(Subgroup.characterRingInduction M (1 : R(M)) : H0 → ℂ), (ξH : H0 → ℂ)⟫ =
          algebraMap ℤ ℂ (n * bM))
    (hprime_sum :
      ∃ bΣ : ℤ,
        ∑ β in ((Finset.univ.erase (1 : (H0 ⧸ M) →* ℂˣ)).filter fun β => β.ker = ⊥),
          ⟪((((β.comp (QuotientGroup.mk' M)).toCharacterRing - 1 : R(H0)) : H0 → ℂ),
              (ξH : H0 → ℂ)⟫ =
          algebraMap ℤ ℂ (n * bΣ))
    (hsmaller :
      ∀ ε : H0 →* ℂˣ, ε ≠ 1 → ε.ker.index < δ.ker.index →
        ∃ bC : ℤ,
          (ε.ker.index : ℂ) * ⟪((1 : R(H0)) : H0 → ℂ), (ξH : H0 → ℂ)⟫ +
            ∑ γ in
                ((Finset.univ.erase
                    (QuotientGroup.lift ε.ker ε (show ε.ker ≤ ε.ker from le_rfl))).filter
                  fun γ => γ.ker = ⊥),
                ⟪((((γ.comp (QuotientGroup.mk' ε.ker)).toCharacterRing - 1 : R(H0)) :
                      H0 → ℂ),
                    (ξH : H0 → ℂ)⟫ =
              algebraMap ℤ ℂ (n * bC)) :
    let Mq : Subgroup (H0 ⧸ δ.ker) := M.map (QuotientGroup.mk' δ.ker)
    let η : R(H0 ⧸ δ.ker) :=
      (δ.ker.index : ℤ) • (1 : R(H0 ⧸ δ.ker)) +
        ∑ γ in
            ((Finset.univ.erase
                (QuotientGroup.lift δ.ker δ (show δ.ker ≤ δ.ker from le_rfl))).filter
              fun γ => γ.ker = ⊥),
            ((γ.toCharacterRing - 1 : R(H0 ⧸ δ.ker)))
    let ηM : R(H0 ⧸ δ.ker) :=
      Subgroup.characterRingInduction Mq (1 : R(Mq)) -
        ∑ β : ((H0 ⧸ δ.ker) ⧸ Mq) →* ℂˣ,
          (((β.comp (QuotientGroup.mk' Mq)).toCharacterRing - 1 : R(H0 ⧸ δ.ker)))
    ∃ bR : ℤ,
      quotient_pullback_pairing_linearMap δ ξH η =
        quotient_pullback_pairing_linearMap δ ξH ηM + algebraMap ℤ ℂ (n * bR) := by
  classical
  dsimp
  have hsplit :
      quotient_pullback_pairing_linearMap δ ξH η =
        quotient_pullback_pairing_linearMap δ ξH ηM +
          ((∑ γ in
              ((Finset.univ.erase
                  (QuotientGroup.lift δ.ker δ (show δ.ker ≤ δ.ker from le_rfl))).filter
                fun γ => γ.ker ≠ ⊥),
              (let ε : H0 →* ℂˣ := γ.comp (QuotientGroup.mk' δ.ker)
               (ε.ker.index : ℂ) * ⟪((1 : R(H0)) : H0 → ℂ), (ξH : H0 → ℂ)⟫ +
                 ∑ θ in
                     ((Finset.univ.erase
                         (QuotientGroup.lift ε.ker ε (show ε.ker ≤ ε.ker from le_rfl))).filter
                       fun θ => θ.ker = ⊥),
                     ⟪((((θ.comp (QuotientGroup.mk' ε.ker)).toCharacterRing - 1 : R(H0)) :
                           H0 → ℂ),
                         (ξH : H0 → ℂ)⟫) -
            quotient_pullback_pairing_linearMap δ ξH (1 : R(H0 ⧸ δ.ker))) := by
    -- Reduce the frontier theorem to the exact source-faithful scalar split.
    simpa [η, ηM] using
      strict_branch_top_layer_pairing_minus_mapped_block_eq_nonfaithful_residual_minus_trivial
        (δ := δ)
        (M := M)
        hδker_lt_M
        hprime
        (ξH := ξH)
  have hresidual :
      ∃ bR : ℤ,
        (∑ γ in
            ((Finset.univ.erase
                (QuotientGroup.lift δ.ker δ (show δ.ker ≤ δ.ker from le_rfl))).filter
              fun γ => γ.ker ≠ ⊥),
            (let ε : H0 →* ℂˣ := γ.comp (QuotientGroup.mk' δ.ker)
             (ε.ker.index : ℂ) * ⟪((1 : R(H0)) : H0 → ℂ), (ξH : H0 → ℂ)⟫ +
               ∑ θ in
                   ((Finset.univ.erase
                       (QuotientGroup.lift ε.ker ε (show ε.ker ≤ ε.ker from le_rfl))).filter
                     fun θ => θ.ker = ⊥),
                   ⟪((((θ.comp (QuotientGroup.mk' ε.ker)).toCharacterRing - 1 : R(H0)) :
                         H0 → ℂ),
                       (ξH : H0 → ℂ)⟫) -
          quotient_pullback_pairing_linearMap δ ξH (1 : R(H0 ⧸ δ.ker)) =
          algebraMap ℤ ℂ (n * bR) := by
    -- The residual arithmetic is already closed once the exceptional trivial branch is removed.
    simpa using
      strict_branch_full_nonfaithful_residual_minus_trivial_divisible
        (δ := δ)
        (M := M)
        hδker_lt_M
        (ξH := ξH)
        hsmaller
  rcases hresidual with ⟨bR, hbR⟩
  refine ⟨bR, ?_⟩
  -- Combine the exact scalar split with the packaged residual divisibility witness.
  calc
    quotient_pullback_pairing_linearMap δ ξH η =
      quotient_pullback_pairing_linearMap δ ξH ηM +
        ((∑ γ in
            ((Finset.univ.erase
                (QuotientGroup.lift δ.ker δ (show δ.ker ≤ δ.ker from le_rfl))).filter
              fun γ => γ.ker ≠ ⊥),
            (let ε : H0 →* ℂˣ := γ.comp (QuotientGroup.mk' δ.ker)
             (ε.ker.index : ℂ) * ⟪((1 : R(H0)) : H0 → ℂ), (ξH : H0 → ℂ)⟫ +
               ∑ θ in
                   ((Finset.univ.erase
                       (QuotientGroup.lift ε.ker ε (show ε.ker ≤ ε.ker from le_rfl))).filter
                     fun θ => θ.ker = ⊥),
                   ⟪((((θ.comp (QuotientGroup.mk' ε.ker)).toCharacterRing - 1 : R(H0)) :
                         H0 → ℂ),
                       (ξH : H0 → ℂ)⟫) -
          quotient_pullback_pairing_linearMap δ ξH (1 : R(H0 ⧸ δ.ker))) := hsplit
    _ =
      quotient_pullback_pairing_linearMap δ ξH ηM + algebraMap ℤ ℂ (n * bR) := by
        rw [hbR]

/-- Helper for Remark 11-11.1-3: in the strict branch `δ.ker < M`, the faithful cyclic layer is
the only remaining owner. The smaller-kernel recursion already packages every nontrivial lift from
`H.1 ⧸ M`, so the unresolved step is now the source-faithful divisibility reassembly at the mapped
coatom rather than the false pairing identity used earlier. -/
private theorem strict_branch_faithful_cyclic_layer_pairing_divisible_owner
    {H0 : Type*} [Group H0] [Finite H0] {n : ℤ}
    (δ : H0 →* ℂˣ)
    (M : Subgroup H0) [M.Normal]
    (hδker_lt_M : δ.ker < M)
    (hprime : (Nat.card (H0 ⧸ M)).Prime)
    (ξH : R(H0))
    (hMpair :
      ∃ bM : ℤ,
        ⟪(Subgroup.characterRingInduction M (1 : R(M)) : H0 → ℂ), (ξH : H0 → ℂ)⟫ =
          algebraMap ℤ ℂ (n * bM))
    (hprime_sum :
      ∃ bΣ : ℤ,
        ∑ β in ((Finset.univ.erase (1 : (H0 ⧸ M) →* ℂˣ)).filter fun β => β.ker = ⊥),
          ⟪((((β.comp (QuotientGroup.mk' M)).toCharacterRing - 1 : R(H0)) : H0 → ℂ),
              (ξH : H0 → ℂ)⟫ =
          algebraMap ℤ ℂ (n * bΣ))
    (hsmaller :
      ∀ ε : H0 →* ℂˣ, ε ≠ 1 → ε.ker.index < δ.ker.index →
        ∃ bC : ℤ,
          (ε.ker.index : ℂ) * ⟪((1 : R(H0)) : H0 → ℂ), (ξH : H0 → ℂ)⟫ +
            ∑ γ in
                ((Finset.univ.erase
                    (QuotientGroup.lift ε.ker ε (show ε.ker ≤ ε.ker from le_rfl))).filter
                  fun γ => γ.ker = ⊥),
                ⟪((((γ.comp (QuotientGroup.mk' ε.ker)).toCharacterRing - 1 : R(H0)) :
                      H0 → ℂ),
                    (ξH : H0 → ℂ)⟫ =
              algebraMap ℤ ℂ (n * bC))) :
    let δq : (H0 ⧸ δ.ker) →* ℂˣ :=
      QuotientGroup.lift δ.ker δ (show δ.ker ≤ δ.ker from le_rfl)
    let η : R(H0 ⧸ δ.ker) :=
      (δ.ker.index : ℤ) • (1 : R(H0 ⧸ δ.ker)) +
        ∑ γ in ((Finset.univ.erase δq).filter fun γ => γ.ker = ⊥),
          ((γ.toCharacterRing - 1 : R(H0 ⧸ δ.ker)))
    ∃ b : ℤ,
      quotient_pullback_pairing_linearMap δ ξH η = algebraMap ℤ ℂ (n * b) := by
  classical
  dsimp
  let Mq : Subgroup (H0 ⧸ δ.ker) := M.map (QuotientGroup.mk' δ.ker)
  let ηM : R(H0 ⧸ δ.ker) :=
    Subgroup.characterRingInduction Mq (1 : R(Mq)) -
      ∑ β : ((H0 ⧸ δ.ker) ⧸ Mq) →* ℂˣ,
        (((β.comp (QuotientGroup.mk' Mq)).toCharacterRing - 1 : R(H0 ⧸ δ.ker)))
  have hmapped_block :
      ∃ b : ℤ,
        quotient_pullback_pairing_linearMap δ ξH ηM =
          algebraMap ℤ ℂ (n * b) := by
    -- The mapped coatom block is already packaged by the induced-trivial term together with the
    -- transported faithful quotient-character family on `H0 / M`.
    simpa [Mq, ηM] using
      strict_branch_mapped_coatom_block_pairing_divisible
        (δ := δ)
        (M := M)
        hδker_lt_M
        hprime
        ξH
        hMpair
        hprime_sum
  have hresidual :
      ∃ bR : ℤ,
        quotient_pullback_pairing_linearMap δ ξH
            ((δ.ker.index : ℤ) • (1 : R(H0 ⧸ δ.ker)) +
              ∑ γ in
                  ((Finset.univ.erase
                      (QuotientGroup.lift δ.ker δ (show δ.ker ≤ δ.ker from le_rfl))).filter
                    fun γ => γ.ker = ⊥),
                  ((γ.toCharacterRing - 1 : R(H0 ⧸ δ.ker)))) =
          quotient_pullback_pairing_linearMap δ ξH ηM + algebraMap ℤ ℂ (n * bR) := by
    -- Route correction: after exposing `hsmaller` in the theorem statement, the only remaining
    -- work is the pairing-level residual decomposition from the full top layer to `ηM`.
    simpa [Mq, ηM] using
      strict_branch_faithful_top_layer_pairing_eq_mapped_block_plus_divisible_residual
        (δ := δ)
        (M := M)
        hδker_lt_M
        hprime
        ξH
        hMpair
        hprime_sum
        hsmaller
  rcases hmapped_block with ⟨bM, hbM⟩
  rcases hresidual with ⟨bR, hbR⟩
  refine ⟨bM + bR, ?_⟩
  -- The residual theorem upgrades the mapped-coatom block to the full faithful top layer, and the
  -- two integer witnesses add.
  calc
    quotient_pullback_pairing_linearMap δ ξH
        ((δ.ker.index : ℤ) • (1 : R(H0 ⧸ δ.ker)) +
          ∑ γ in
              ((Finset.univ.erase
                  (QuotientGroup.lift δ.ker δ (show δ.ker ≤ δ.ker from le_rfl))).filter
                fun γ => γ.ker = ⊥),
              ((γ.toCharacterRing - 1 : R(H0 ⧸ δ.ker)))) =
      quotient_pullback_pairing_linearMap δ ξH ηM + algebraMap ℤ ℂ (n * bR) := hbR
    _ = algebraMap ℤ ℂ (n * bM) + algebraMap ℤ ℂ (n * bR) := by
          rw [hbM]
    _ = algebraMap ℤ ℂ (n * (bM + bR)) := by
          simp [Int.cast_mul, Int.cast_add, mul_add, add_comm, add_left_comm, add_assoc]

/-- Helper for Remark 11-11.1-3: in the strict branch `δ.ker < M`, the faithful cyclic layer is
the only remaining owner. The smaller-kernel recursion already packages every nontrivial lift from
`H.1 ⧸ M`, so the unresolved step is now the source-faithful divisibility reassembly at the mapped
coatom rather than the false pairing identity used earlier. -/
private theorem strict_kernel_growth_faithful_layer_divisible
    (X : Finset (Subgroup G))
    (hXelem : ∀ H : Subgroup G, H ∈ X ↔ IsElementary H)
    {x : (H : X) → R(H.1)} {t : elementary_coherence_target X hXelem} {n : ℤ}
    (hdx : elementary_coherence_defect X hXelem x = n • t)
    (H : X)
    (sH : ((J : (Finset.univ : Finset (Subgroup H.1))) → R(J.1)) →ₗ[ℤ] R(H.1))
    (hsH : Function.LeftInverse sH
      (Representation.characterRingRestriction (Finset.univ : Finset (Subgroup H.1))).toLinearMap)
    (hproper :
      ∀ (J : Subgroup H.1) (hJ : J < ⊤) (α : J →* ℂˣ),
        let KX : X := ⟨J.map H.1.subtype,
          (hXelem (J.map H.1.subtype)).2 <|
            isElementary_of_mulEquiv_local
              (J.equivMapOfInjective H.1.subtype H.1.subtype_injective)
              (subgroup_isElementary_of_isElementary_local J ((hXelem H.1).1 H.2))⟩
        ∃ c : ℤ, linear_character_pairing_int H.1 J α (x KX) = n * c)
    (δ : H.1 →* ℂˣ) (hδ : δ ≠ 1)
    (hm :
      ∀ ε : H.1 →* ℂˣ, ε ≠ 1 → ε.ker.index < δ.ker.index →
        let XH : Finset (Subgroup H.1) := Finset.univ
        let ψH : (J : XH) → R(J.1) := fun J ↦
          Subgroup.characterRingTransport
            (J.1.equivMapOfInjective H.1.subtype H.1.subtype_injective)
            (x ⟨J.1.map H.1.subtype,
              (hXelem (J.1.map H.1.subtype)).2 <|
                isElementary_of_mulEquiv_local
                  (J.1.equivMapOfInjective H.1.subtype H.1.subtype_injective)
                  (subgroup_isElementary_of_isElementary_local J.1 ((hXelem H.1).1 H.2))⟩)
        let εq : (H.1 ⧸ ε.ker) →* ℂˣ :=
          QuotientGroup.lift ε.ker ε (show ε.ker ≤ ε.ker from le_rfl)
        let term : ((H.1 ⧸ ε.ker) →* ℂˣ) → ℂ := fun γ ↦
          ⟪((((γ.comp (QuotientGroup.mk' ε.ker)).toCharacterRing - 1 : R(H.1)) :
                H.1 → ℂ),
              ((sH ψH : R(H.1)) : H.1 → ℂ)⟫
        ∃ bC : ℤ,
          (ε.ker.index : ℂ) * ⟪((1 : R(H.1)) : H.1 → ℂ), ((sH ψH : R(H.1)) : H.1 → ℂ)⟫ +
            ∑ γ in ((Finset.univ.erase εq).filter fun γ => γ.ker = ⊥), term γ =
              algebraMap ℤ ℂ (n * bC))
    (M : Subgroup H.1) (hM : IsCoatom M)
    (hδker_lt_M : δ.ker < M) :
    let XH : Finset (Subgroup H.1) := Finset.univ
    let ψH : (J : XH) → R(J.1) := fun J ↦
      Subgroup.characterRingTransport
        (J.1.equivMapOfInjective H.1.subtype H.1.subtype_injective)
        (x ⟨J.1.map H.1.subtype,
          (hXelem (J.1.map H.1.subtype)).2 <|
            isElementary_of_mulEquiv_local
              (J.1.equivMapOfInjective H.1.subtype H.1.subtype_injective)
              (subgroup_isElementary_of_isElementary_local J.1 ((hXelem H.1).1 H.2))⟩)
    let ξH : R(H.1) := sH ψH
    ∃ bC : ℤ,
      (δ.ker.index : ℂ) * ⟪((1 : R(H.1)) : H.1 → ℂ), (ξH : H.1 → ℂ)⟫ +
        ∑ γ in
            ((Finset.univ.erase
                (QuotientGroup.lift δ.ker δ (show δ.ker ≤ δ.ker from le_rfl))).filter
              fun γ => γ.ker = ⊥),
            ⟪((((γ.comp (QuotientGroup.mk' δ.ker)).toCharacterRing - 1 : R(H.1)) :
                  H.1 → ℂ),
                (ξH : H.1 → ℂ)⟫ =
          algebraMap ℤ ℂ (n * bC) := by
  classical
  dsimp
  let ψH : (J : (Finset.univ : Finset (Subgroup H.1))) → R(J.1) := fun J ↦
    Subgroup.characterRingTransport
      (J.1.equivMapOfInjective H.1.subtype H.1.subtype_injective)
      (x ⟨J.1.map H.1.subtype,
        (hXelem (J.1.map H.1.subtype)).2 <|
          isElementary_of_mulEquiv_local
            (J.1.equivMapOfInjective H.1.subtype H.1.subtype_injective)
            (subgroup_isElementary_of_isElementary_local J.1 ((hXelem H.1).1 H.2))⟩)
  let ξH : R(H.1) := sH ψH
  have hprime :
      (Nat.card (H.1 ⧸ M)).Prime :=
    prime_card_quotient_of_isCoatom_of_isElementary M hM ((hXelem H.1).1 H.2)
  have hMpair :
      ∃ bM : ℤ,
        ⟪(Subgroup.characterRingInduction M (1 : R(M)) : H.1 → ℂ), (ξH : H.1 → ℂ)⟫ =
          algebraMap ℤ ℂ (n * bM) := by
    -- The chosen coatom remains a proper subgroup, so the local proper branch already controls
    -- its induced-trivial pairing.
    simpa [ψH, ξH] using
      proper_induced_pairing_divisible_of_transport_pairing_int_divisible
        X hXelem hdx H sH hsH M (1 : M →* ℂˣ) (hproper M hM.lt_top (1 : M →* ℂˣ))
  have hstrict_lift_difference :
      ∀ β : (H.1 ⧸ M) →* ℂˣ, β ≠ 1 →
        ∃ bβ : ℤ,
          ⟪((((β.comp (QuotientGroup.mk' M)).toCharacterRing - 1 : R(H.1)) : H.1 → ℂ),
              (ξH : H.1 → ℂ)⟫ =
            algebraMap ℤ ℂ (n * bβ) := by
    intro β hβ
    -- The smaller-kernel package already controls every nontrivial lift from the prime quotient.
    exact
      prime_coatom_lift_difference_pairing_divisible_from_smaller_kernel_package
        (δ := δ)
        (M := M)
        hδker_lt_M
        hprime
        ξH
        hMpair
        (fun ε hε hlt ↦ by
          simpa [ξH] using hm ε hε hlt)
        β
        hβ
  have hprime_sum :
      ∃ bΣ : ℤ,
        ∑ β in ((Finset.univ.erase (1 : (H.1 ⧸ M) →* ℂˣ)).filter fun β => β.ker = ⊥),
          ⟪((((β.comp (QuotientGroup.mk' M)).toCharacterRing - 1 : R(H.1)) : H.1 → ℂ),
              (ξH : H.1 → ℂ)⟫ =
          algebraMap ℤ ℂ (n * bΣ) := by
    -- Package the lifted prime-quotient differences before the final strict-branch reassembly.
    exact
      prime_quotient_faithful_lift_difference_sum_divisible
        (M := M)
        hprime
        ξH
        hstrict_lift_difference
  letI : Group.IsNilpotent H.1 := by
    rcases (hXelem H.1).1 H.2 with ⟨p, hp⟩
    exact IsPElementary.isNilpotent hp
  letI : M.Normal :=
    Subgroup.NormalizerCondition.normal_of_coatom
      (G := H.1) (H := M) (normalizerCondition_of_isNilpotent (G := H.1)) hM
  letI : IsSimpleGroup (H.1 ⧸ M) :=
    isSimpleGroup_quotient_of_isCoatom (G := H.1) M hM
  have hcomm : ∀ a b : H.1 ⧸ M, a * b = b * a :=
    IsSimpleGroup.comm_iff_isSolvable.mpr inferInstance
  letI : CommGroup (H.1 ⧸ M) :=
    { QuotientGroup.Quotient.group M with
      mul_comm := hcomm }
  letI : Fintype ((H.1 ⧸ M) →* ℂˣ) := linearCharacterFintype
  let Mq : Subgroup (H.1 ⧸ δ.ker) := M.map (QuotientGroup.mk' δ.ker)
  let e : ((H.1 ⧸ δ.ker) ⧸ Mq) ≃* H.1 ⧸ M :=
    QuotientGroup.quotientQuotientEquivQuotient δ.ker M hδker_lt_M.le
  letI : CommGroup ((H.1 ⧸ δ.ker) ⧸ Mq) :=
    { QuotientGroup.Quotient.group Mq with
      mul_comm := by
        intro a b
        apply e.injective
        simpa [e] using hcomm (e a) (e b) }
  letI : Fintype (((H.1 ⧸ δ.ker) ⧸ Mq) →* ℂˣ) := linearCharacterFintype
  have hfaithful_top_rewrite :
      let δq : (H.1 ⧸ δ.ker) →* ℂˣ :=
        QuotientGroup.lift δ.ker δ (show δ.ker ≤ δ.ker from le_rfl)
      let η : R(H.1 ⧸ δ.ker) :=
        (δ.ker.index : ℤ) • (1 : R(H.1 ⧸ δ.ker)) +
          ∑ γ in ((Finset.univ.erase δq).filter fun γ => γ.ker = ⊥),
            ((γ.toCharacterRing - 1 : R(H.1 ⧸ δ.ker)))
      (δ.ker.index : ℂ) * ⟪((1 : R(H.1)) : H.1 → ℂ), (ξH : H.1 → ℂ)⟫ +
          ∑ γ in ((Finset.univ.erase δq).filter fun γ => γ.ker = ⊥),
            ⟪((((γ.comp (QuotientGroup.mk' δ.ker)).toCharacterRing - 1 : R(H.1)) :
                  H.1 → ℂ),
                (ξH : H.1 → ℂ)⟫ =
        quotient_pullback_pairing_linearMap δ ξH η := by
    -- Keep the target in its quotient-pullback form so the remaining blocker is a single
    -- quotient-side divisibility statement for the faithful top-layer element `η`.
    simpa [ξH] using
      faithful_quotient_top_layer_eq_quotient_pullback_pairing
        (β := δ)
        (ξ := ξH)
  have howner :
      let δq : (H.1 ⧸ δ.ker) →* ℂˣ :=
        QuotientGroup.lift δ.ker δ (show δ.ker ≤ δ.ker from le_rfl)
      let η : R(H.1 ⧸ δ.ker) :=
        (δ.ker.index : ℤ) • (1 : R(H.1 ⧸ δ.ker)) +
          ∑ γ in ((Finset.univ.erase δq).filter fun γ => γ.ker = ⊥),
            ((γ.toCharacterRing - 1 : R(H.1 ⧸ δ.ker)))
      ∃ b : ℤ,
        quotient_pullback_pairing_linearMap δ ξH η = algebraMap ℤ ℂ (n * b) := by
    -- Route correction: reduce the strict branch to the single quotient-side owner theorem.
    exact
      strict_branch_faithful_cyclic_layer_pairing_divisible_owner
        (δ := δ)
        (M := M)
        hδker_lt_M
        hprime
        ξH
        hMpair
        hprime_sum
        (fun ε hε hlt ↦ by
          simpa [ξH] using hm ε hε hlt)
  -- Rewrite the quotient-side owner theorem back to the displayed faithful cyclic-layer scalar.
  exact
    faithful_quotient_top_layer_divisible_of_pullback_divisible
      (β := δ)
      (ξ := ξH)
      howner

/-- Helper for Remark 11-11.1-3: in the chosen-coatom context, the equality branch
`δ.ker = M` should produce the distinguished ambient difference witness directly at pairing
level. This keeps the missing source-faithful construction attached to the richer local context
instead of the abstract prime-coatom splitter. -/
private theorem fixed_coatom_top_difference_pairing_divisible_without_kernel_growth_cycle
    (X : Finset (Subgroup G))
    (hXelem : ∀ H : Subgroup G, H ∈ X ↔ IsElementary H)
    {x : (H : X) → R(H.1)} {t : elementary_coherence_target X hXelem} {n : ℤ}
    (hdx : elementary_coherence_defect X hXelem x = n • t)
    (H : X)
    (sH : ((J : (Finset.univ : Finset (Subgroup H.1))) → R(J.1)) →ₗ[ℤ] R(H.1))
    (hsH : Function.LeftInverse sH
      (Representation.characterRingRestriction (Finset.univ : Finset (Subgroup H.1))).toLinearMap)
    (hproper :
      ∀ (J : Subgroup H.1) (hJ : J < ⊤) (α : J →* ℂˣ),
        let KX : X := ⟨J.map H.1.subtype,
          (hXelem (J.map H.1.subtype)).2 <|
            isElementary_of_mulEquiv_local
              (J.equivMapOfInjective H.1.subtype H.1.subtype_injective)
              (subgroup_isElementary_of_isElementary_local J ((hXelem H.1).1 H.2))⟩
        ∃ c : ℤ, linear_character_pairing_int H.1 J α (x KX) = n * c)
    (δ : H.1 →* ℂˣ) (hδ : δ ≠ 1)
    (M : Subgroup H.1) (hM : IsCoatom M)
    (hEq : δ.ker = M) :
    let XH : Finset (Subgroup H.1) := Finset.univ
    let ψH : (J : XH) → R(J.1) := fun J ↦
      Subgroup.characterRingTransport
        (J.1.equivMapOfInjective H.1.subtype H.1.subtype_injective)
        (x ⟨J.1.map H.1.subtype,
          (hXelem (J.1.map H.1.subtype)).2 <|
            isElementary_of_mulEquiv_local
              (J.1.equivMapOfInjective H.1.subtype H.1.subtype_injective)
              (subgroup_isElementary_of_isElementary_local J.1 ((hXelem H.1).1 H.2))⟩)
    let ξH : R(H.1) := sH ψH
    ∃ bδ : ℤ,
      ⟪((((δ.toCharacterRing - 1 : R(H.1)) : H.1 → ℂ)), (ξH : H.1 → ℂ)⟫ =
        algebraMap ℤ ℂ (n * bδ) := by
  classical
  dsimp
  -- Route correction: the equality branch should be closed from the fixed-coatom package itself,
  -- rather than by looping back through the ambient kernel-growth owner.
  let ψH : (J : (Finset.univ : Finset (Subgroup H.1))) → R(J.1) := fun J ↦
    Subgroup.characterRingTransport
      (J.1.equivMapOfInjective H.1.subtype H.1.subtype_injective)
      (x ⟨J.1.map H.1.subtype,
        (hXelem (J.1.map H.1.subtype)).2 <|
          isElementary_of_mulEquiv_local
            (J.1.equivMapOfInjective H.1.subtype H.1.subtype_injective)
            (subgroup_isElementary_of_isElementary_local J.1 ((hXelem H.1).1 H.2))⟩)
  let ξH : R(H.1) := sH ψH
  letI : M.Normal := hEq ▸ (inferInstance : δ.ker.Normal)
  have hprime :
      (Nat.card (H.1 ⧸ M)).Prime :=
    prime_card_quotient_of_isCoatom_of_isElementary M hM ((hXelem H.1).1 H.2)
  have hMpair :
      ∃ bM : ℤ,
        ⟪(Subgroup.characterRingInduction M (1 : R(M)) : H.1 → ℂ), (ξH : H.1 → ℂ)⟫ =
          algebraMap ℤ ℂ (n * bM) := by
    -- The fixed coatom remains a proper subgroup, so the proper-branch theorem supplies its
    -- induced-trivial pairing witness.
    simpa [ψH, ξH] using
      proper_induced_pairing_divisible_of_transport_pairing_int_divisible
        X hXelem hdx H sH hsH M (1 : M →* ℂˣ) (hproper M hM.lt_top (1 : M →* ℂˣ))
  have hαδ : δ.comp Subgroup.topEquiv.toMonoidHom ≠ 1 := by
    -- The transported top character is still nontrivial.
    simpa using top_subgroup_character_nontrivial_of_ambient_nontrivial δ hδ
  letI : Group.IsNilpotent H.1 := by
    rcases (hXelem H.1).1 H.2 with ⟨p, hp⟩
    exact IsPElementary.isNilpotent hp
  letI : IsSimpleGroup (H.1 ⧸ M) :=
    isSimpleGroup_quotient_of_isCoatom (G := H.1) M hM
  have hcomm : ∀ a b : H.1 ⧸ M, a * b = b * a :=
    IsSimpleGroup.comm_iff_isSolvable.mpr inferInstance
  letI : CommGroup (H.1 ⧸ M) :=
    { QuotientGroup.Quotient.group M with
      mul_comm := hcomm }
  letI : Fintype ((H.1 ⧸ M) →* ℂˣ) := linearCharacterFintype
  have hpair_rewrite :
      ⟪(Subgroup.characterRingInduction M (1 : R(M)) : H.1 → ℂ), (ξH : H.1 → ℂ)⟫ =
        (M.index : ℂ) * ⟪((1 : R(H.1)) : H.1 → ℂ), (ξH : H.1 → ℂ)⟫ +
          ∑ β : (H.1 ⧸ M) →* ℂˣ,
            ⟪((((β.comp (QuotientGroup.mk' M)).toCharacterRing - 1 : R(H.1)) : H.1 → ℂ),
                (ξH : H.1 → ℂ)⟫ := by
    -- Rewrite the coatom-induced trivial pairing as its trivial-line contribution plus the
    -- quotient-character difference sum.
    simpa [ξH] using
      induced_trivial_pairing_eq_index_trivial_pairing_add_quotient_difference_sum
        (M := M) hcomm (ξ := ξH)
  have hquotdiff :
      ∀ β : (H.1 ⧸ M) →* ℂˣ,
        ∃ bβ : ℤ,
          ⟪((((β.comp (QuotientGroup.mk' M)).toCharacterRing - 1 : R(H.1)) : H.1 → ℂ),
              (ξH : H.1 → ℂ)⟫ =
            algebraMap ℤ ℂ (n * bβ) := by
    intro β
    let α : (⊤ : Subgroup H.1) →* ℂˣ :=
      (β.comp (QuotientGroup.mk' M)).comp Subgroup.topEquiv.symm.toMonoidHom
    by_cases hα : α = 1
    · refine ⟨0, ?_⟩
      have hambient_zero :
          (((β.comp (QuotientGroup.mk' M)).toCharacterRing - 1 : R(H.1))) = 0 := by
        calc
          (((β.comp (QuotientGroup.mk' M)).toCharacterRing - 1 : R(H.1))) =
              Subgroup.characterRingInduction (⊤ : Subgroup H.1) (α.toCharacterRing - 1) := by
                symm
                simpa [α] using top_induced_difference_eq_ambient_difference (H0 := H.1) α
          _ = 0 := by
                rw [hα]
                simp
      simp [hambient_zero]
    · rcases
        top_difference_pairing_divisible_of_nontrivial_top_character_via_kernel_quotient_recursion
          X hXelem hdx H sH hsH hproper α hα with
        ⟨bβ, hbβ⟩
      refine ⟨bβ, ?_⟩
      calc
        ⟪((((β.comp (QuotientGroup.mk' M)).toCharacterRing - 1 : R(H.1)) : H.1 → ℂ),
            (ξH : H.1 → ℂ)⟫ =
          ⟪((Subgroup.characterRingInduction (⊤ : Subgroup H.1)
                (α.toCharacterRing - 1) : R(H.1)) : H.1 → ℂ),
              (ξH : H.1 → ℂ)⟫ := by
                simpa [α] using
                  ambient_difference_pairing_eq_top_induced_difference_pairing
                    (ξ := ξH) α
        _ = algebraMap ℤ ℂ (n * bβ) := hbβ
  have htopdiff :
      ∀ α : (⊤ : Subgroup H.1) →* ℂˣ, α ≠ 1 →
        ∃ b : ℤ,
          ⟪((Subgroup.characterRingInduction (⊤ : Subgroup H.1)
                (α.toCharacterRing - 1) : R(H.1)) : H.1 → ℂ),
              (ξH : H.1 → ℂ)⟫ =
            algebraMap ℤ ℂ (n * b) := by
    intro α hα
    -- The nontrivial top-character branch is already owned by the kernel-quotient recursion.
    exact
      top_difference_pairing_divisible_of_nontrivial_top_character_via_kernel_quotient_recursion
        X hXelem hdx H sH hsH hproper α hα
  have hfixed_coatom :
      (∃ b₀ : ℤ,
        (M.index : ℂ) * ⟪((1 : R(H.1)) : H.1 → ℂ), (ξH : H.1 → ℂ)⟫ =
          algebraMap ℤ ℂ (n * b₀)) ∧
        ∀ α : (⊤ : Subgroup H.1) →* ℂˣ,
          ∃ b : ℤ,
            ⟪((Subgroup.characterRingInduction (⊤ : Subgroup H.1)
                  (α.toCharacterRing - 1) : R(H.1)) : H.1 → ℂ),
                (ξH : H.1 → ℂ)⟫ =
              algebraMap ℤ ℂ (n * b) := by
    -- Package the fixed coatom once, separating the scaled trivial line from the top characters.
    exact
      coatom_top_local_pairing_divisible_package_of_fixed_coatom
        M hcomm ξH hMpair hpair_rewrite hquotdiff htopdiff hprime
  obtain ⟨bδ, hbδ⟩ := hfixed_coatom.2 (δ.comp Subgroup.topEquiv.toMonoidHom)
  refine ⟨bδ, ?_⟩
  -- Rewrite the ambient difference for `δ` as the top-induced difference for its transported top
  -- character, then apply the fixed-coatom package.
  calc
    ⟪((((δ.toCharacterRing - 1 : R(H.1)) : H.1 → ℂ)), (ξH : H.1 → ℂ)⟫ =
      ⟪((Subgroup.characterRingInduction (⊤ : Subgroup H.1)
            ((δ.comp Subgroup.topEquiv.toMonoidHom).toCharacterRing - 1) : R(H.1)) : H.1 → ℂ),
          (ξH : H.1 → ℂ)⟫ := by
            simpa using
              (ambient_difference_pairing_eq_top_induced_difference_pairing
                (ξ := ξH) (δ.comp Subgroup.topEquiv.toMonoidHom)).symm
    _ = algebraMap ℤ ℂ (n * bδ) := hbδ

/-- Helper for Remark 11-11.1-3: in the chosen-coatom context, the equality branch
`δ.ker = M` should produce the distinguished ambient difference witness directly at pairing
level. This keeps the missing source-faithful construction attached to the richer local context
instead of the abstract prime-coatom splitter. -/
private theorem top_subgroup_character_nontrivial_of_ambient_nontrivial
    {H0 : Type*} [Group H0]
    (δ : H0 →* ℂˣ) (hδ : δ ≠ 1) :
    δ.comp Subgroup.topEquiv.toMonoidHom ≠ 1 := by
  intro htop
  apply hδ
  ext x
  have htop_eval := congrFun (congrArg MonoidHom.toFun htop) ⟨x, by simp⟩
  simpa using htop_eval

/-- Helper for Remark 11-11.1-3: in the chosen-coatom context, the equality branch
`δ.ker = M` should produce the distinguished ambient difference witness directly at pairing
level. This keeps the missing source-faithful construction attached to the richer local context
instead of the abstract prime-coatom splitter. -/
private theorem prime_quotient_faithful_cyclic_layer_pairing_divisible
    (X : Finset (Subgroup G))
    (hXelem : ∀ H : Subgroup G, H ∈ X ↔ IsElementary H)
    {x : (H : X) → R(H.1)} {t : elementary_coherence_target X hXelem} {n : ℤ}
    (hdx : elementary_coherence_defect X hXelem x = n • t)
    (H : X)
    (sH : ((J : (Finset.univ : Finset (Subgroup H.1))) → R(J.1)) →ₗ[ℤ] R(H.1))
    (hsH : Function.LeftInverse sH
      (Representation.characterRingRestriction (Finset.univ : Finset (Subgroup H.1))).toLinearMap)
    (hproper :
      ∀ (J : Subgroup H.1) (hJ : J < ⊤) (α : J →* ℂˣ),
        let KX : X := ⟨J.map H.1.subtype,
          (hXelem (J.map H.1.subtype)).2 <|
            isElementary_of_mulEquiv_local
              (J.equivMapOfInjective H.1.subtype H.1.subtype_injective)
              (subgroup_isElementary_of_isElementary_local J ((hXelem H.1).1 H.2))⟩
        ∃ c : ℤ, linear_character_pairing_int H.1 J α (x KX) = n * c)
    (δ : H.1 →* ℂˣ) (hδ : δ ≠ 1)
    (M : Subgroup H.1) (hM : IsCoatom M)
    (hEq : δ.ker = M) :
    let XH : Finset (Subgroup H.1) := Finset.univ
    let ψH : (J : XH) → R(J.1) := fun J ↦
      Subgroup.characterRingTransport
        (J.1.equivMapOfInjective H.1.subtype H.1.subtype_injective)
        (x ⟨J.1.map H.1.subtype,
          (hXelem (J.1.map H.1.subtype)).2 <|
            isElementary_of_mulEquiv_local
              (J.1.equivMapOfInjective H.1.subtype H.1.subtype_injective)
              (subgroup_isElementary_of_isElementary_local J.1 ((hXelem H.1).1 H.2))⟩)
    let ξH : R(H.1) := sH ψH
    ∃ bC : ℤ,
      (δ.ker.index : ℂ) * ⟪((1 : R(H.1)) : H.1 → ℂ), (ξH : H.1 → ℂ)⟫ +
        ∑ γ in ((Finset.univ.erase
            (QuotientGroup.lift δ.ker δ (show δ.ker ≤ δ.ker from le_rfl))).filter
          fun γ => γ.ker = ⊥),
          ⟪((((γ.comp (QuotientGroup.mk' δ.ker)).toCharacterRing - 1 : R(H.1)) :
                H.1 → ℂ),
              (ξH : H.1 → ℂ)⟫ =
        algebraMap ℤ ℂ (n * bC) := by
  classical
  dsimp
  let ψH : (J : (Finset.univ : Finset (Subgroup H.1))) → R(J.1) := fun J ↦
    Subgroup.characterRingTransport
      (J.1.equivMapOfInjective H.1.subtype H.1.subtype_injective)
      (x ⟨J.1.map H.1.subtype,
        (hXelem (J.1.map H.1.subtype)).2 <|
          isElementary_of_mulEquiv_local
            (J.1.equivMapOfInjective H.1.subtype H.1.subtype_injective)
            (subgroup_isElementary_of_isElementary_local J.1 ((hXelem H.1).1 H.2))⟩)
  let ξH : R(H.1) := sH ψH
  letI : M.Normal := hEq ▸ (inferInstance : δ.ker.Normal)
  have hprime :
      (Nat.card (H.1 ⧸ M)).Prime :=
    prime_card_quotient_of_isCoatom_of_isElementary M hM ((hXelem H.1).1 H.2)
  have hMpair :
      ∃ bM : ℤ,
        ⟪(Subgroup.characterRingInduction M (1 : R(M)) : H.1 → ℂ), (ξH : H.1 → ℂ)⟫ =
          algebraMap ℤ ℂ (n * bM) := by
    -- The chosen coatom remains a proper subgroup, so the local proper branch already controls
    -- its induced-trivial pairing.
    simpa [ψH, ξH] using
      proper_induced_pairing_divisible_of_transport_pairing_int_divisible
        X hXelem hdx H sH hsH M (1 : M →* ℂˣ) (hproper M hM.lt_top (1 : M →* ℂˣ))
  have hdiff :
      ∃ bδ : ℤ,
        ⟪((((δ.toCharacterRing - 1 : R(H.1)) : H.1 → ℂ)), (ξH : H.1 → ℂ)⟫ =
          algebraMap ℤ ℂ (n * bδ) := by
    -- Delegate the remaining equality-branch blocker to the dedicated fixed-coatom helper so the
    -- current theorem only packages the prime-coatom cyclic layer.
    simpa [ψH, ξH] using
      fixed_coatom_top_difference_pairing_divisible_without_kernel_growth_cycle
        X hXelem hdx H sH hsH hproper δ hδ M hM hEq
  -- Once the distinguished ambient difference witness is available, the equality branch is
  -- exactly the previously isolated coatom package.
  exact
    prime_coatom_kernel_eq_branch_of_difference_divisible
      δ hδ M ξH hEq hprime hMpair hdiff

/-- Helper for Remark 11-11.1-3: in the chosen-coatom context, the equality branch
`δ.ker = M` should produce the distinguished ambient difference witness directly at pairing
level. This keeps the missing source-faithful construction attached to the richer local context
instead of the abstract prime-coatom splitter. -/
private theorem coatom_kernel_eq_difference_pairing_divisible
    (X : Finset (Subgroup G))
    (hXelem : ∀ H : Subgroup G, H ∈ X ↔ IsElementary H)
    {x : (H : X) → R(H.1)} {t : elementary_coherence_target X hXelem} {n : ℤ}
    (hdx : elementary_coherence_defect X hXelem x = n • t)
    (H : X)
    (sH : ((J : (Finset.univ : Finset (Subgroup H.1))) → R(J.1)) →ₗ[ℤ] R(H.1))
    (hsH : Function.LeftInverse sH
      (Representation.characterRingRestriction (Finset.univ : Finset (Subgroup H.1))).toLinearMap)
    (hproper :
      ∀ (J : Subgroup H.1) (hJ : J < ⊤) (α : J →* ℂˣ),
        let KX : X := ⟨J.map H.1.subtype,
          (hXelem (J.map H.1.subtype)).2 <|
            isElementary_of_mulEquiv_local
              (J.equivMapOfInjective H.1.subtype H.1.subtype_injective)
              (subgroup_isElementary_of_isElementary_local J ((hXelem H.1).1 H.2))⟩
        ∃ c : ℤ, linear_character_pairing_int H.1 J α (x KX) = n * c)
    (δ : H.1 →* ℂˣ) (hδ : δ ≠ 1)
    (M : Subgroup H.1) (hM : IsCoatom M)
    (hEq : δ.ker = M) :
    let XH : Finset (Subgroup H.1) := Finset.univ
    let ψH : (J : XH) → R(J.1) := fun J ↦
      Subgroup.characterRingTransport
        (J.1.equivMapOfInjective H.1.subtype H.1.subtype_injective)
        (x ⟨J.1.map H.1.subtype,
          (hXelem (J.1.map H.1.subtype)).2 <|
            isElementary_of_mulEquiv_local
              (J.1.equivMapOfInjective H.1.subtype H.1.subtype_injective)
              (subgroup_isElementary_of_isElementary_local J.1 ((hXelem H.1).1 H.2))⟩)
    let ξH : R(H.1) := sH ψH
    ∃ bδ : ℤ,
      ⟪((((δ.toCharacterRing - 1 : R(H.1)) : H.1 → ℂ)), (ξH : H.1 → ℂ)⟫ =
        algebraMap ℤ ℂ (n * bδ) := by
  classical
  let ψH : (J : (Finset.univ : Finset (Subgroup H.1))) → R(J.1) := fun J ↦
    Subgroup.characterRingTransport
      (J.1.equivMapOfInjective H.1.subtype H.1.subtype_injective)
      (x ⟨J.1.map H.1.subtype,
        (hXelem (J.1.map H.1.subtype)).2 <|
          isElementary_of_mulEquiv_local
            (J.1.equivMapOfInjective H.1.subtype H.1.subtype_injective)
            (subgroup_isElementary_of_isElementary_local J.1 ((hXelem H.1).1 H.2))⟩)
  let ξH : R(H.1) := sH ψH
  letI : M.Normal := hEq ▸ (inferInstance : δ.ker.Normal)
  have hprime :
      (Nat.card (H.1 ⧸ M)).Prime :=
    prime_card_quotient_of_isCoatom_of_isElementary M hM ((hXelem H.1).1 H.2)
  have hMpair :
      ∃ bM : ℤ,
        ⟪(Subgroup.characterRingInduction M (1 : R(M)) : H.1 → ℂ), (ξH : H.1 → ℂ)⟫ =
          algebraMap ℤ ℂ (n * bM) := by
    -- The chosen coatom is already a proper subgroup, so its induced-trivial pairing is part of
    -- the established local proper branch.
    simpa [ψH, ξH] using
      proper_induced_pairing_divisible_of_transport_pairing_int_divisible
        X hXelem hdx H sH hsH M (1 : M →* ℂˣ) (hproper M hM.lt_top (1 : M →* ℂˣ))
  have hcyclic :
      ∃ bC : ℤ,
        (δ.ker.index : ℂ) * ⟪((1 : R(H.1)) : H.1 → ℂ), (ξH : H.1 → ℂ)⟫ +
          ∑ γ in ((Finset.univ.erase
              (QuotientGroup.lift δ.ker δ (show δ.ker ≤ δ.ker from le_rfl))).filter
            fun γ => γ.ker = ⊥),
            ⟪((((γ.comp (QuotientGroup.mk' δ.ker)).toCharacterRing - 1 : R(H.1)) :
                  H.1 → ℂ),
                (ξH : H.1 → ℂ)⟫ =
          algebraMap ℤ ℂ (n * bC) := by
    -- Route correction: the quotient-span route is false on a prime quotient. The remaining owner
    -- is the direct prime-quotient package for the faithful cyclic layer itself.
    simpa [ψH, ξH] using
      prime_quotient_faithful_cyclic_layer_pairing_divisible
        X hXelem hdx H sH hsH hproper δ hδ M hM hEq
  -- Once the faithful cyclic layer is packaged, the reverse coatom identity recovers the
  -- distinguished ambient difference witness.
  simpa [ψH, ξH] using
    difference_divisible_of_kernel_eq_chosen_coatom_of_faithful_cyclic_layer_divisible
      δ hδ M ξH hEq hprime hMpair hcyclic

/-- Helper for Remark 11-11.1-3: the faithful cyclic-quotient package should be proved by strong
induction on the kernel index, not by a false quotient-side span statement. -/
private theorem chosen_coatom_faithful_cyclic_layer_step
    (X : Finset (Subgroup G))
    (hXelem : ∀ H : Subgroup G, H ∈ X ↔ IsElementary H)
    {x : (H : X) → R(H.1)} {t : elementary_coherence_target X hXelem} {n : ℤ}
    (hdx : elementary_coherence_defect X hXelem x = n • t)
    (H : X)
    (sH : ((J : (Finset.univ : Finset (Subgroup H.1))) → R(J.1)) →ₗ[ℤ] R(H.1))
    (hsH : Function.LeftInverse sH
      (Representation.characterRingRestriction (Finset.univ : Finset (Subgroup H.1))).toLinearMap)
    (hproper :
      ∀ (J : Subgroup H.1) (hJ : J < ⊤) (α : J →* ℂˣ),
        let KX : X := ⟨J.map H.1.subtype,
          (hXelem (J.map H.1.subtype)).2 <|
            isElementary_of_mulEquiv_local
              (J.equivMapOfInjective H.1.subtype H.1.subtype_injective)
              (subgroup_isElementary_of_isElementary_local J ((hXelem H.1).1 H.2))⟩
        ∃ c : ℤ, linear_character_pairing_int H.1 J α (x KX) = n * c)
    (δ : H.1 →* ℂˣ) (hδ : δ ≠ 1)
    (hm :
      ∀ ε : H.1 →* ℂˣ, ε ≠ 1 → ε.ker.index < δ.ker.index →
        let XH : Finset (Subgroup H.1) := Finset.univ
        let ψH : (J : XH) → R(J.1) := fun J ↦
          Subgroup.characterRingTransport
            (J.1.equivMapOfInjective H.1.subtype H.1.subtype_injective)
            (x ⟨J.1.map H.1.subtype,
              (hXelem (J.1.map H.1.subtype)).2 <|
                isElementary_of_mulEquiv_local
                  (J.1.equivMapOfInjective H.1.subtype H.1.subtype_injective)
                  (subgroup_isElementary_of_isElementary_local J.1 ((hXelem H.1).1 H.2))⟩)
        let εq : (H.1 ⧸ ε.ker) →* ℂˣ :=
          QuotientGroup.lift ε.ker ε (show ε.ker ≤ ε.ker from le_rfl)
        let term : ((H.1 ⧸ ε.ker) →* ℂˣ) → ℂ := fun γ ↦
          ⟪((((γ.comp (QuotientGroup.mk' ε.ker)).toCharacterRing - 1 : R(H.1)) :
                H.1 → ℂ),
              ((sH ψH : R(H.1)) : H.1 → ℂ)⟫
        ∃ bC : ℤ,
          (ε.ker.index : ℂ) * ⟪((1 : R(H.1)) : H.1 → ℂ), ((sH ψH : R(H.1)) : H.1 → ℂ)⟫ +
            ∑ γ in ((Finset.univ.erase εq).filter fun γ => γ.ker = ⊥), term γ =
              algebraMap ℤ ℂ (n * bC))
    (M : Subgroup H.1) (hM : IsCoatom M) (hδker_le_M : δ.ker ≤ M) :
    let XH : Finset (Subgroup H.1) := Finset.univ
    let ψH : (J : XH) → R(J.1) := fun J ↦
      Subgroup.characterRingTransport
        (J.1.equivMapOfInjective H.1.subtype H.1.subtype_injective)
        (x ⟨J.1.map H.1.subtype,
          (hXelem (J.1.map H.1.subtype)).2 <|
            isElementary_of_mulEquiv_local
              (J.1.equivMapOfInjective H.1.subtype H.1.subtype_injective)
              (subgroup_isElementary_of_isElementary_local J.1 ((hXelem H.1).1 H.2))⟩)
    let ξH : R(H.1) := sH ψH
    ∃ bC : ℤ,
      (δ.ker.index : ℂ) * ⟪((1 : R(H.1)) : H.1 → ℂ), (ξH : H.1 → ℂ)⟫ +
        ∑ γ in
            ((Finset.univ.erase
                (QuotientGroup.lift δ.ker δ (show δ.ker ≤ δ.ker from le_rfl))).filter
              fun γ => γ.ker = ⊥),
            ⟪((((γ.comp (QuotientGroup.mk' δ.ker)).toCharacterRing - 1 : R(H.1)) :
                  H.1 → ℂ),
                (ξH : H.1 → ℂ)⟫ =
          algebraMap ℤ ℂ (n * bC) := by
  classical
  dsimp
  let ψH : (J : (Finset.univ : Finset (Subgroup H.1))) → R(J.1) := fun J ↦
    Subgroup.characterRingTransport
      (J.1.equivMapOfInjective H.1.subtype H.1.subtype_injective)
      (x ⟨J.1.map H.1.subtype,
        (hXelem (J.1.map H.1.subtype)).2 <|
          isElementary_of_mulEquiv_local
            (J.1.equivMapOfInjective H.1.subtype H.1.subtype_injective)
            (subgroup_isElementary_of_isElementary_local J.1 ((hXelem H.1).1 H.2))⟩)
  let ξH : R(H.1) := sH ψH
  rcases lt_or_eq_of_le hδker_le_M with hδker_lt_M | hEq
  · -- Route correction: the strict branch now goes directly through the smaller-kernel owner, so
    -- the false prime-coatom reassembly helper is no longer part of the recursion.
    simpa [ψH, ξH] using
      strict_kernel_growth_faithful_layer_divisible
        X hXelem hdx H sH hsH hproper δ hδ hm M hM hδker_lt_M
  · -- The equality branch remains the repaired prime-quotient package based on the fixed coatom.
    simpa [ψH, ξH] using
      prime_quotient_faithful_cyclic_layer_pairing_divisible
        X hXelem hdx H sH hsH hproper δ hδ M hM hEq

/-- Helper for Remark 11-11.1-3: the faithful cyclic-quotient package should be proved by strong
induction on the kernel index, not by a false quotient-side span statement. -/
private theorem cyclic_faithful_layer_pairing_divisible_by_kernel_index_induction
    (X : Finset (Subgroup G))
    (hXelem : ∀ H : Subgroup G, H ∈ X ↔ IsElementary H)
    {x : (H : X) → R(H.1)} {t : elementary_coherence_target X hXelem} {n : ℤ}
    (hdx : elementary_coherence_defect X hXelem x = n • t)
    (H : X)
    (sH : ((J : (Finset.univ : Finset (Subgroup H.1))) → R(J.1)) →ₗ[ℤ] R(H.1))
    (hsH : Function.LeftInverse sH
      (Representation.characterRingRestriction (Finset.univ : Finset (Subgroup H.1))).toLinearMap)
    (hproper :
      ∀ (J : Subgroup H.1) (hJ : J < ⊤) (α : J →* ℂˣ),
        let KX : X := ⟨J.map H.1.subtype,
          (hXelem (J.map H.1.subtype)).2 <|
            isElementary_of_mulEquiv_local
              (J.equivMapOfInjective H.1.subtype H.1.subtype_injective)
              (subgroup_isElementary_of_isElementary_local J ((hXelem H.1).1 H.2))⟩
        ∃ c : ℤ, linear_character_pairing_int H.1 J α (x KX) = n * c)
    (β : H.1 →* ℂˣ) (hβ : β ≠ 1) :
    let XH : Finset (Subgroup H.1) := Finset.univ
    let ψH : (J : XH) → R(J.1) := fun J ↦
      Subgroup.characterRingTransport
        (J.1.equivMapOfInjective H.1.subtype H.1.subtype_injective)
        (x ⟨J.1.map H.1.subtype,
          (hXelem (J.1.map H.1.subtype)).2 <|
            isElementary_of_mulEquiv_local
              (J.1.equivMapOfInjective H.1.subtype H.1.subtype_injective)
              (subgroup_isElementary_of_isElementary_local J.1 ((hXelem H.1).1 H.2))⟩)
    let βq : (H.1 ⧸ β.ker) →* ℂˣ :=
      QuotientGroup.lift β.ker β (show β.ker ≤ β.ker from le_rfl)
    let term : ((H.1 ⧸ β.ker) →* ℂˣ) → ℂ := fun γ ↦
      ⟪((((γ.comp (QuotientGroup.mk' β.ker)).toCharacterRing - 1 : R(H.1)) :
            H.1 → ℂ),
          ((sH ψH : R(H.1)) : H.1 → ℂ)⟫
    ∃ bC : ℤ,
      (β.ker.index : ℂ) * ⟪((1 : R(H.1)) : H.1 → ℂ), ((sH ψH : R(H.1)) : H.1 → ℂ)⟫ +
        ∑ γ in ((Finset.univ.erase βq).filter fun γ => γ.ker = ⊥), term γ =
          algebraMap ℤ ℂ (n * bC) := by
  classical
  dsimp
  let P : ℕ → Prop := fun m =>
    ∀ δ : H.1 →* ℂˣ, δ ≠ 1 → δ.ker.index = m →
      let XH : Finset (Subgroup H.1) := Finset.univ
      let ψH : (J : XH) → R(J.1) := fun J ↦
        Subgroup.characterRingTransport
          (J.1.equivMapOfInjective H.1.subtype H.1.subtype_injective)
          (x ⟨J.1.map H.1.subtype,
            (hXelem (J.1.map H.1.subtype)).2 <|
              isElementary_of_mulEquiv_local
                (J.1.equivMapOfInjective H.1.subtype H.1.subtype_injective)
                (subgroup_isElementary_of_isElementary_local J.1 ((hXelem H.1).1 H.2))⟩)
      let δq : (H.1 ⧸ δ.ker) →* ℂˣ :=
        QuotientGroup.lift δ.ker δ (show δ.ker ≤ δ.ker from le_rfl)
      let term : ((H.1 ⧸ δ.ker) →* ℂˣ) → ℂ := fun γ ↦
        ⟪((((γ.comp (QuotientGroup.mk' δ.ker)).toCharacterRing - 1 : R(H.1)) :
              H.1 → ℂ),
            ((sH ψH : R(H.1)) : H.1 → ℂ)⟫
      ∃ bC : ℤ,
        (δ.ker.index : ℂ) * ⟪((1 : R(H.1)) : H.1 → ℂ), ((sH ψH : R(H.1)) : H.1 → ℂ)⟫ +
          ∑ γ in ((Finset.univ.erase δq).filter fun γ => γ.ker = ⊥), term γ =
            algebraMap ℤ ℂ (n * bC)
  have hP : ∀ m : ℕ, P m := by
    intro m
    refine Nat.strong_induction_on m ?_
    intro m hm δ hδ hδindex
    have hδker_top : δ.ker ≠ ⊤ := by
      intro hker
      apply hδ
      ext x
      have hxker : x ∈ δ.ker := by
        rw [hker]
        simp
      simpa [MonoidHom.mem_ker] using hxker
    obtain ⟨M, hM, hδker_le_M⟩ :=
      (eq_top_or_exists_le_coatom δ.ker).resolve_left hδker_top
    have hstep :=
      chosen_coatom_faithful_cyclic_layer_step
        X hXelem hdx H sH hsH hproper δ hδ
        (fun ε hε hlt ↦ hm ε.ker.index (by simpa [hδindex] using hlt) ε hε rfl)
        M hM hδker_le_M
    simpa [P, ψH, ξH] using hstep
  -- Evaluate the strong-induction owner at the given nontrivial character `β`.
  exact hP β.ker.index β hβ rfl

/-- Helper for Remark 11-11.1-3: the cyclic quotient owner theorem should package the kernel-index
trivial line together with the faithful erased quotient-character summands directly from the proper
quotient-subgroup branch, without passing through the false raw span statement. -/
private theorem cyclic_quotient_top_layer_pairing_divisible_of_local_proper_branch
    (X : Finset (Subgroup G))
    (hXelem : ∀ H : Subgroup G, H ∈ X ↔ IsElementary H)
    {x : (H : X) → R(H.1)} {t : elementary_coherence_target X hXelem} {n : ℤ}
    (hdx : elementary_coherence_defect X hXelem x = n • t)
    (H : X)
    (sH : ((J : (Finset.univ : Finset (Subgroup H.1))) → R(J.1)) →ₗ[ℤ] R(H.1))
    (hsH : Function.LeftInverse sH
      (Representation.characterRingRestriction (Finset.univ : Finset (Subgroup H.1))).toLinearMap)
    (hproper :
      ∀ (J : Subgroup H.1) (hJ : J < ⊤) (α : J →* ℂˣ),
        let KX : X := ⟨J.map H.1.subtype,
          (hXelem (J.map H.1.subtype)).2 <|
            isElementary_of_mulEquiv_local
              (J.equivMapOfInjective H.1.subtype H.1.subtype_injective)
              (subgroup_isElementary_of_isElementary_local J ((hXelem H.1).1 H.2))⟩
        ∃ c : ℤ, linear_character_pairing_int H.1 J α (x KX) = n * c)
    (β : H.1 →* ℂˣ) (hβ : β ≠ 1) :
    let XH : Finset (Subgroup H.1) := Finset.univ
    let ψH : (J : XH) → R(J.1) := fun J ↦
      Subgroup.characterRingTransport
        (J.1.equivMapOfInjective H.1.subtype H.1.subtype_injective)
        (x ⟨J.1.map H.1.subtype,
          (hXelem (J.1.map H.1.subtype)).2 <|
            isElementary_of_mulEquiv_local
              (J.1.equivMapOfInjective H.1.subtype H.1.subtype_injective)
              (subgroup_isElementary_of_isElementary_local J.1 ((hXelem H.1).1 H.2))⟩)
    let βq : (H.1 ⧸ β.ker) →* ℂˣ :=
      QuotientGroup.lift β.ker β (show β.ker ≤ β.ker from le_rfl)
    let term : ((H.1 ⧸ β.ker) →* ℂˣ) → ℂ := fun γ ↦
      ⟪((((γ.comp (QuotientGroup.mk' β.ker)).toCharacterRing - 1 : R(H.1)) :
            H.1 → ℂ),
          ((sH ψH : R(H.1)) : H.1 → ℂ)⟫
    ∃ bC : ℤ,
      (β.ker.index : ℂ) * ⟪((1 : R(H.1)) : H.1 → ℂ), ((sH ψH : R(H.1)) : H.1 → ℂ)⟫ +
        ∑ γ in ((Finset.univ.erase βq).filter fun γ => γ.ker = ⊥), term γ =
          algebraMap ℤ ℂ (n * bC) := by
  -- Route correction: the quotient-side span owner is false. The main theorem is now just the
  -- interface wrapper around the kernel-index induction owner for the faithful cyclic layer.
  simpa using
    cyclic_faithful_layer_pairing_divisible_by_kernel_index_induction
      X hXelem hdx H sH hsH hproper β hβ

/-- Helper for Remark 11-11.1-3: the cyclic quotient's top layer must be packaged as one block.
This is the source-faithful replacement for the failed attempt to prove the scaled trivial line and
the faithful erased quotient-character sum separately. -/
private theorem kernel_scaled_trivial_plus_faithful_erased_sum_divisible
    (X : Finset (Subgroup G))
    (hXelem : ∀ H : Subgroup G, H ∈ X ↔ IsElementary H)
    {x : (H : X) → R(H.1)} {t : elementary_coherence_target X hXelem} {n : ℤ}
    (hdx : elementary_coherence_defect X hXelem x = n • t)
    (H : X)
    (sH : ((J : (Finset.univ : Finset (Subgroup H.1))) → R(J.1)) →ₗ[ℤ] R(H.1))
    (hsH : Function.LeftInverse sH
      (Representation.characterRingRestriction (Finset.univ : Finset (Subgroup H.1))).toLinearMap)
    (hproper :
      ∀ (J : Subgroup H.1) (hJ : J < ⊤) (α : J →* ℂˣ),
        let KX : X := ⟨J.map H.1.subtype,
          (hXelem (J.map H.1.subtype)).2 <|
            isElementary_of_mulEquiv_local
              (J.equivMapOfInjective H.1.subtype H.1.subtype_injective)
              (subgroup_isElementary_of_isElementary_local J ((hXelem H.1).1 H.2))⟩
        ∃ c : ℤ, linear_character_pairing_int H.1 J α (x KX) = n * c)
    (β : H.1 →* ℂˣ) (hβ : β ≠ 1) :
    let XH : Finset (Subgroup H.1) := Finset.univ
    let ψH : (J : XH) → R(J.1) := fun J ↦
      Subgroup.characterRingTransport
        (J.1.equivMapOfInjective H.1.subtype H.1.subtype_injective)
        (x ⟨J.1.map H.1.subtype,
          (hXelem (J.1.map H.1.subtype)).2 <|
            isElementary_of_mulEquiv_local
              (J.1.equivMapOfInjective H.1.subtype H.1.subtype_injective)
              (subgroup_isElementary_of_isElementary_local J.1 ((hXelem H.1).1 H.2))⟩)
    let βq : (H.1 ⧸ β.ker) →* ℂˣ :=
      QuotientGroup.lift β.ker β (show β.ker ≤ β.ker from le_rfl)
    let term : ((H.1 ⧸ β.ker) →* ℂˣ) → ℂ := fun γ ↦
      ⟪((((γ.comp (QuotientGroup.mk' β.ker)).toCharacterRing - 1 : R(H.1)) :
            H.1 → ℂ),
          ((sH ψH : R(H.1)) : H.1 → ℂ)⟫
    ∃ bC : ℤ,
      (β.ker.index : ℂ) * ⟪((1 : R(H.1)) : H.1 → ℂ), ((sH ψH : R(H.1)) : H.1 → ℂ)⟫ +
        ∑ γ in ((Finset.univ.erase βq).filter fun γ => γ.ker = ⊥), term γ =
          algebraMap ℤ ℂ (n * bC) := by
  classical
  dsimp
  -- The only remaining owner is the direct cyclic-quotient divisibility package; the false
  -- interval-span rewrite layer has been removed entirely.
  simpa using
    cyclic_quotient_top_layer_pairing_divisible_of_local_proper_branch
      X hXelem hdx H sH hsH hproper β hβ

/-- Helper for Remark 11-11.1-3: one strong-induction step for the nontrivial ambient-character
owner theorem. The source-faithful decomposition is the induced trivial pairing at `β.ker`,
followed by a split between faithful erased quotient characters and the true smaller-kernel
branches. -/
private theorem ambient_difference_pairing_divisible_kernel_growth_step
    (X : Finset (Subgroup G))
    (hXelem : ∀ H : Subgroup G, H ∈ X ↔ IsElementary H)
    {x : (H : X) → R(H.1)} {t : elementary_coherence_target X hXelem} {n : ℤ}
    (hdx : elementary_coherence_defect X hXelem x = n • t)
    (H : X)
    (sH : ((J : (Finset.univ : Finset (Subgroup H.1))) → R(J.1)) →ₗ[ℤ] R(H.1))
    (hsH : Function.LeftInverse sH
      (Representation.characterRingRestriction (Finset.univ : Finset (Subgroup H.1))).toLinearMap)
    (hproper :
      ∀ (J : Subgroup H.1) (hJ : J < ⊤) (α : J →* ℂˣ),
        let KX : X := ⟨J.map H.1.subtype,
          (hXelem (J.map H.1.subtype)).2 <|
            isElementary_of_mulEquiv_local
              (J.equivMapOfInjective H.1.subtype H.1.subtype_injective)
              (subgroup_isElementary_of_isElementary_local J ((hXelem H.1).1 H.2))⟩
        ∃ c : ℤ, linear_character_pairing_int H.1 J α (x KX) = n * c)
    (β : H.1 →* ℂˣ) (hβ : β ≠ 1)
    (ih :
      ∀ δ : H.1 →* ℂˣ, δ ≠ 1 → δ.ker.index < β.ker.index →
        let XH : Finset (Subgroup H.1) := Finset.univ
        let ψH : (J : XH) → R(J.1) := fun J ↦
          Subgroup.characterRingTransport
            (J.1.equivMapOfInjective H.1.subtype H.1.subtype_injective)
            (x ⟨J.1.map H.1.subtype,
              (hXelem (J.1.map H.1.subtype)).2 <|
                isElementary_of_mulEquiv_local
                  (J.1.equivMapOfInjective H.1.subtype H.1.subtype_injective)
                  (subgroup_isElementary_of_isElementary_local J.1 ((hXelem H.1).1 H.2))⟩)
        ∃ b : ℤ,
          ⟪((((δ.toCharacterRing - 1 : R(H.1)) : H.1 → ℂ)),
              ((sH ψH : R(H.1)) : H.1 → ℂ)⟫ =
            algebraMap ℤ ℂ (n * b)) :
    let XH : Finset (Subgroup H.1) := Finset.univ
    let ψH : (J : XH) → R(J.1) := fun J ↦
      Subgroup.characterRingTransport
        (J.1.equivMapOfInjective H.1.subtype H.1.subtype_injective)
        (x ⟨J.1.map H.1.subtype,
          (hXelem (J.1.map H.1.subtype)).2 <|
            isElementary_of_mulEquiv_local
              (J.1.equivMapOfInjective H.1.subtype H.1.subtype_injective)
              (subgroup_isElementary_of_isElementary_local J.1 ((hXelem H.1).1 H.2))⟩)
    ∃ b : ℤ,
      ⟪((((β.toCharacterRing - 1 : R(H.1)) : H.1 → ℂ)),
          ((sH ψH : R(H.1)) : H.1 → ℂ)⟫ =
        algebraMap ℤ ℂ (n * b) := by
  classical
  dsimp at ih ⊢
  let βq : (H.1 ⧸ β.ker) →* ℂˣ :=
    QuotientGroup.lift β.ker β (show β.ker ≤ β.ker from le_rfl)
  let term : ((H.1 ⧸ β.ker) →* ℂˣ) → ℂ := fun γ ↦
    ⟪((((γ.comp (QuotientGroup.mk' β.ker)).toCharacterRing - 1 : R(H.1)) :
          H.1 → ℂ),
        ((sH
            (fun J ↦
              Subgroup.characterRingTransport
                (J.1.equivMapOfInjective H.1.subtype H.1.subtype_injective)
                (x ⟨J.1.map H.1.subtype,
                  (hXelem (J.1.map H.1.subtype)).2 <|
                    isElementary_of_mulEquiv_local
                      (J.1.equivMapOfInjective H.1.subtype H.1.subtype_injective)
                      (subgroup_isElementary_of_isElementary_local J.1
                        ((hXelem H.1).1 H.2))⟩)) : R(H.1)) : H.1 → ℂ)⟫
  have hNF :=
    nonfaithful_erased_quotient_sum_divisible
      X hXelem H sH β ih
  have hβker : β.ker < ⊤ := by
    refine lt_top_iff_ne_top.mpr ?_
    intro hker
    apply hβ
    ext x
    have hxker : x ∈ β.ker := by
      rw [hker]
      simp
    simpa [MonoidHom.mem_ker] using hxker
  have hkernel_input :
      let KX : X := ⟨β.ker.map H.1.subtype,
        (hXelem (β.ker.map H.1.subtype)).2 <|
          isElementary_of_mulEquiv_local
            (β.ker.equivMapOfInjective H.1.subtype H.1.subtype_injective)
            (subgroup_isElementary_of_isElementary_local β.ker ((hXelem H.1).1 H.2))⟩
      ∃ c : ℤ, linear_character_pairing_int H.1 β.ker (1 : β.ker →* ℂˣ) (x KX) = n * c := by
    -- The kernel branch starts from the proper-subgroup arithmetic witness supplied by `hproper`.
    simpa using hproper β.ker hβker (1 : β.ker →* ℂˣ)
  have hkernel :=
    kernel_branch_transport_target_normal_form
      X hXelem hdx H sH hsH β hkernel_input
  have hfaithful :=
    kernel_scaled_trivial_plus_faithful_erased_sum_divisible
      X hXelem hdx H sH hsH hproper β hβ
  have hsum_split :
      ∑ γ in Finset.univ.erase βq, term γ =
        ∑ γ in ((Finset.univ.erase βq).filter fun γ => γ.ker = ⊥), term γ +
          ∑ γ in ((Finset.univ.erase βq).filter fun γ => γ.ker ≠ ⊥), term γ := by
    -- Split the erased quotient-character family into faithful and nonfaithful branches.
    simpa using
      (Finset.sum_filter_add_sum_filter_not
        (s := Finset.univ.erase βq)
        (f := term)
        (p := fun γ : (H.1 ⧸ β.ker) →* ℂˣ => γ.ker = ⊥)).symm
  rcases hkernel with ⟨bK, hbK⟩
  rcases hfaithful with ⟨bC, hbC⟩
  rcases hNF with ⟨bNF, hbNF⟩
  refine ⟨bK - bC - bNF, ?_⟩
  have htarget :
      ⟪((((β.toCharacterRing - 1 : R(H.1)) : H.1 → ℂ)),
          ((sH
              (fun J ↦
                Subgroup.characterRingTransport
                  (J.1.equivMapOfInjective H.1.subtype H.1.subtype_injective)
                  (x ⟨J.1.map H.1.subtype,
                    (hXelem (J.1.map H.1.subtype)).2 <|
                      isElementary_of_mulEquiv_local
                        (J.1.equivMapOfInjective H.1.subtype H.1.subtype_injective)
                        (subgroup_isElementary_of_isElementary_local J.1
                          ((hXelem H.1).1 H.2))⟩)) : R(H.1)) : H.1 → ℂ)⟫ =
        (⟪(Subgroup.characterRingInduction β.ker (1 : R(β.ker)) : H.1 → ℂ),
            ((sH
                (fun J ↦
                  Subgroup.characterRingTransport
                    (J.1.equivMapOfInjective H.1.subtype H.1.subtype_injective)
                    (x ⟨J.1.map H.1.subtype,
                      (hXelem (J.1.map H.1.subtype)).2 <|
                        isElementary_of_mulEquiv_local
                          (J.1.equivMapOfInjective H.1.subtype H.1.subtype_injective)
                          (subgroup_isElementary_of_isElementary_local J.1
                            ((hXelem H.1).1 H.2))⟩)) : R(H.1)) : H.1 → ℂ)⟫ -
          ((β.ker.index : ℂ) *
              ⟪((1 : R(H.1)) : H.1 → ℂ),
                  ((sH
                      (fun J ↦
                        Subgroup.characterRingTransport
                          (J.1.equivMapOfInjective H.1.subtype H.1.subtype_injective)
                          (x ⟨J.1.map H.1.subtype,
                            (hXelem (J.1.map H.1.subtype)).2 <|
                              isElementary_of_mulEquiv_local
                                (J.1.equivMapOfInjective H.1.subtype H.1.subtype_injective)
                                (subgroup_isElementary_of_isElementary_local J.1
                                  ((hXelem H.1).1 H.2))⟩)) : R(H.1)) : H.1 → ℂ)⟫ +
            ∑ γ in ((Finset.univ.erase βq).filter fun γ => γ.ker = ⊥), term γ) -
          ∑ γ in ((Finset.univ.erase βq).filter fun γ => γ.ker ≠ ⊥), term γ := by
    have hdecomp :=
      kernel_induced_pairing_decomposes_with_distinguished_difference
        (β := β)
        (ξ := sH
          (fun J ↦
            Subgroup.characterRingTransport
              (J.1.equivMapOfInjective H.1.subtype H.1.subtype_injective)
              (x ⟨J.1.map H.1.subtype,
                (hXelem (J.1.map H.1.subtype)).2 <|
                  isElementary_of_mulEquiv_local
                    (J.1.equivMapOfInjective H.1.subtype H.1.subtype_injective)
                    (subgroup_isElementary_of_isElementary_local J.1
                      ((hXelem H.1).1 H.2))⟩))
    have hdecomp_split :
        ⟪(Subgroup.characterRingInduction β.ker (1 : R(β.ker)) : H.1 → ℂ),
            ((sH
                (fun J ↦
                  Subgroup.characterRingTransport
                    (J.1.equivMapOfInjective H.1.subtype H.1.subtype_injective)
                    (x ⟨J.1.map H.1.subtype,
                      (hXelem (J.1.map H.1.subtype)).2 <|
                        isElementary_of_mulEquiv_local
                          (J.1.equivMapOfInjective H.1.subtype H.1.subtype_injective)
                          (subgroup_isElementary_of_isElementary_local J.1
                            ((hXelem H.1).1 H.2))⟩)) : R(H.1)) : H.1 → ℂ)⟫ =
          ((β.ker.index : ℂ) *
              ⟪((1 : R(H.1)) : H.1 → ℂ),
                  ((sH
                      (fun J ↦
                        Subgroup.characterRingTransport
                          (J.1.equivMapOfInjective H.1.subtype H.1.subtype_injective)
                          (x ⟨J.1.map H.1.subtype,
                            (hXelem (J.1.map H.1.subtype)).2 <|
                              isElementary_of_mulEquiv_local
                                (J.1.equivMapOfInjective H.1.subtype H.1.subtype_injective)
                                (subgroup_isElementary_of_isElementary_local J.1
                                  ((hXelem H.1).1 H.2))⟩)) : R(H.1)) : H.1 → ℂ)⟫ +
            ∑ γ in ((Finset.univ.erase βq).filter fun γ => γ.ker = ⊥), term γ) +
            ⟪((((β.toCharacterRing - 1 : R(H.1)) : H.1 → ℂ)),
                ((sH
                    (fun J ↦
                      Subgroup.characterRingTransport
                        (J.1.equivMapOfInjective H.1.subtype H.1.subtype_injective)
                        (x ⟨J.1.map H.1.subtype,
                          (hXelem (J.1.map H.1.subtype)).2 <|
                            isElementary_of_mulEquiv_local
                              (J.1.equivMapOfInjective H.1.subtype H.1.subtype_injective)
                              (subgroup_isElementary_of_isElementary_local J.1
                                ((hXelem H.1).1 H.2))⟩)) : R(H.1)) : H.1 → ℂ)⟫ +
            ∑ γ in ((Finset.univ.erase βq).filter fun γ => γ.ker ≠ ⊥), term γ := by
      calc
        ⟪(Subgroup.characterRingInduction β.ker (1 : R(β.ker)) : H.1 → ℂ),
            ((sH
                (fun J ↦
                  Subgroup.characterRingTransport
                    (J.1.equivMapOfInjective H.1.subtype H.1.subtype_injective)
                    (x ⟨J.1.map H.1.subtype,
                      (hXelem (J.1.map H.1.subtype)).2 <|
                        isElementary_of_mulEquiv_local
                          (J.1.equivMapOfInjective H.1.subtype H.1.subtype_injective)
                          (subgroup_isElementary_of_isElementary_local J.1
                            ((hXelem H.1).1 H.2))⟩)) : R(H.1)) : H.1 → ℂ)⟫ =
            (β.ker.index : ℂ) *
                ⟪((1 : R(H.1)) : H.1 → ℂ),
                    ((sH
                        (fun J ↦
                          Subgroup.characterRingTransport
                            (J.1.equivMapOfInjective H.1.subtype H.1.subtype_injective)
                            (x ⟨J.1.map H.1.subtype,
                              (hXelem (J.1.map H.1.subtype)).2 <|
                                isElementary_of_mulEquiv_local
                                  (J.1.equivMapOfInjective H.1.subtype H.1.subtype_injective)
                                  (subgroup_isElementary_of_isElementary_local J.1
                                    ((hXelem H.1).1 H.2))⟩)) : R(H.1)) : H.1 → ℂ)⟫ +
              ⟪((((β.toCharacterRing - 1 : R(H.1)) : H.1 → ℂ)),
                  ((sH
                      (fun J ↦
                        Subgroup.characterRingTransport
                          (J.1.equivMapOfInjective H.1.subtype H.1.subtype_injective)
                          (x ⟨J.1.map H.1.subtype,
                            (hXelem (J.1.map H.1.subtype)).2 <|
                              isElementary_of_mulEquiv_local
                                (J.1.equivMapOfInjective H.1.subtype H.1.subtype_injective)
                                (subgroup_isElementary_of_isElementary_local J.1
                                  ((hXelem H.1).1 H.2))⟩)) : R(H.1)) : H.1 → ℂ)⟫ +
                ∑ γ in Finset.univ.erase βq, term γ := by
              simpa [βq, term] using hdecomp
        _ =
            (β.ker.index : ℂ) *
                ⟪((1 : R(H.1)) : H.1 → ℂ),
                    ((sH
                        (fun J ↦
                          Subgroup.characterRingTransport
                            (J.1.equivMapOfInjective H.1.subtype H.1.subtype_injective)
                            (x ⟨J.1.map H.1.subtype,
                              (hXelem (J.1.map H.1.subtype)).2 <|
                                isElementary_of_mulEquiv_local
                                  (J.1.equivMapOfInjective H.1.subtype H.1.subtype_injective)
                                  (subgroup_isElementary_of_isElementary_local J.1
                                    ((hXelem H.1).1 H.2))⟩)) : R(H.1)) : H.1 → ℂ)⟫ +
              ⟪((((β.toCharacterRing - 1 : R(H.1)) : H.1 → ℂ)),
                  ((sH
                      (fun J ↦
                        Subgroup.characterRingTransport
                          (J.1.equivMapOfInjective H.1.subtype H.1.subtype_injective)
                          (x ⟨J.1.map H.1.subtype,
                            (hXelem (J.1.map H.1.subtype)).2 <|
                              isElementary_of_mulEquiv_local
                                (J.1.equivMapOfInjective H.1.subtype H.1.subtype_injective)
                                (subgroup_isElementary_of_isElementary_local J.1
                                  ((hXelem H.1).1 H.2))⟩)) : R(H.1)) : H.1 → ℂ)⟫ +
                (∑ γ in ((Finset.univ.erase βq).filter fun γ => γ.ker = ⊥), term γ +
                  ∑ γ in ((Finset.univ.erase βq).filter fun γ => γ.ker ≠ ⊥), term γ) := by
              rw [hsum_split]
        _ =
            ((β.ker.index : ℂ) *
                ⟪((1 : R(H.1)) : H.1 → ℂ),
                    ((sH
                        (fun J ↦
                          Subgroup.characterRingTransport
                            (J.1.equivMapOfInjective H.1.subtype H.1.subtype_injective)
                            (x ⟨J.1.map H.1.subtype,
                              (hXelem (J.1.map H.1.subtype)).2 <|
                                isElementary_of_mulEquiv_local
                                  (J.1.equivMapOfInjective H.1.subtype H.1.subtype_injective)
                                  (subgroup_isElementary_of_isElementary_local J.1
                                    ((hXelem H.1).1 H.2))⟩)) : R(H.1)) : H.1 → ℂ)⟫ +
              ∑ γ in ((Finset.univ.erase βq).filter fun γ => γ.ker = ⊥), term γ) +
              ⟪((((β.toCharacterRing - 1 : R(H.1)) : H.1 → ℂ)),
                  ((sH
                      (fun J ↦
                        Subgroup.characterRingTransport
                          (J.1.equivMapOfInjective H.1.subtype H.1.subtype_injective)
                          (x ⟨J.1.map H.1.subtype,
                            (hXelem (J.1.map H.1.subtype)).2 <|
                              isElementary_of_mulEquiv_local
                                (J.1.equivMapOfInjective H.1.subtype H.1.subtype_injective)
                                (subgroup_isElementary_of_isElementary_local J.1
                                  ((hXelem H.1).1 H.2))⟩)) : R(H.1)) : H.1 → ℂ)⟫ +
              ∑ γ in ((Finset.univ.erase βq).filter fun γ => γ.ker ≠ ⊥), term γ := by
              ring
    have htarget_plus :
        (⟪((((β.toCharacterRing - 1 : R(H.1)) : H.1 → ℂ)),
            ((sH
                (fun J ↦
                  Subgroup.characterRingTransport
                    (J.1.equivMapOfInjective H.1.subtype H.1.subtype_injective)
                    (x ⟨J.1.map H.1.subtype,
                      (hXelem (J.1.map H.1.subtype)).2 <|
                        isElementary_of_mulEquiv_local
                          (J.1.equivMapOfInjective H.1.subtype H.1.subtype_injective)
                          (subgroup_isElementary_of_isElementary_local J.1
                            ((hXelem H.1).1 H.2))⟩)) : R(H.1)) : H.1 → ℂ)⟫ +
          ∑ γ in ((Finset.univ.erase βq).filter fun γ => γ.ker ≠ ⊥), term γ) =
        ⟪(Subgroup.characterRingInduction β.ker (1 : R(β.ker)) : H.1 → ℂ),
            ((sH
                (fun J ↦
                  Subgroup.characterRingTransport
                    (J.1.equivMapOfInjective H.1.subtype H.1.subtype_injective)
                    (x ⟨J.1.map H.1.subtype,
                      (hXelem (J.1.map H.1.subtype)).2 <|
                        isElementary_of_mulEquiv_local
                          (J.1.equivMapOfInjective H.1.subtype H.1.subtype_injective)
                          (subgroup_isElementary_of_isElementary_local J.1
                            ((hXelem H.1).1 H.2))⟩)) : R(H.1)) : H.1 → ℂ)⟫ -
          ((β.ker.index : ℂ) *
              ⟪((1 : R(H.1)) : H.1 → ℂ),
                  ((sH
                      (fun J ↦
                        Subgroup.characterRingTransport
                          (J.1.equivMapOfInjective H.1.subtype H.1.subtype_injective)
                          (x ⟨J.1.map H.1.subtype,
                            (hXelem (J.1.map H.1.subtype)).2 <|
                              isElementary_of_mulEquiv_local
                                (J.1.equivMapOfInjective H.1.subtype H.1.subtype_injective)
                                (subgroup_isElementary_of_isElementary_local J.1
                                  ((hXelem H.1).1 H.2))⟩)) : R(H.1)) : H.1 → ℂ)⟫ +
            ∑ γ in ((Finset.univ.erase βq).filter fun γ => γ.ker = ⊥), term γ) := by
      apply eq_sub_iff_add_eq.mpr
      simpa [add_assoc, add_left_comm, add_comm] using hdecomp_split.symm
    exact eq_sub_iff_add_eq.mpr htarget_plus
  -- Subtract the two packaged `n`-multiples from the induced-kernel witness to isolate the
  -- distinguished ambient difference term.
  calc
    ⟪((((β.toCharacterRing - 1 : R(H.1)) : H.1 → ℂ)),
        ((sH
            (fun J ↦
              Subgroup.characterRingTransport
                (J.1.equivMapOfInjective H.1.subtype H.1.subtype_injective)
                (x ⟨J.1.map H.1.subtype,
                  (hXelem (J.1.map H.1.subtype)).2 <|
                    isElementary_of_mulEquiv_local
                      (J.1.equivMapOfInjective H.1.subtype H.1.subtype_injective)
                      (subgroup_isElementary_of_isElementary_local J.1
                        ((hXelem H.1).1 H.2))⟩)) : R(H.1)) : H.1 → ℂ)⟫ =
        (⟪(Subgroup.characterRingInduction β.ker (1 : R(β.ker)) : H.1 → ℂ),
            ((sH
                (fun J ↦
                  Subgroup.characterRingTransport
                    (J.1.equivMapOfInjective H.1.subtype H.1.subtype_injective)
                    (x ⟨J.1.map H.1.subtype,
                      (hXelem (J.1.map H.1.subtype)).2 <|
                        isElementary_of_mulEquiv_local
                          (J.1.equivMapOfInjective H.1.subtype H.1.subtype_injective)
                          (subgroup_isElementary_of_isElementary_local J.1
                            ((hXelem H.1).1 H.2))⟩)) : R(H.1)) : H.1 → ℂ)⟫ -
          ((β.ker.index : ℂ) *
              ⟪((1 : R(H.1)) : H.1 → ℂ),
                  ((sH
                      (fun J ↦
                        Subgroup.characterRingTransport
                          (J.1.equivMapOfInjective H.1.subtype H.1.subtype_injective)
                          (x ⟨J.1.map H.1.subtype,
                            (hXelem (J.1.map H.1.subtype)).2 <|
                              isElementary_of_mulEquiv_local
                                (J.1.equivMapOfInjective H.1.subtype H.1.subtype_injective)
                                (subgroup_isElementary_of_isElementary_local J.1
                                  ((hXelem H.1).1 H.2))⟩)) : R(H.1)) : H.1 → ℂ)⟫ +
            ∑ γ in ((Finset.univ.erase βq).filter fun γ => γ.ker = ⊥), term γ) -
          ∑ γ in ((Finset.univ.erase βq).filter fun γ => γ.ker ≠ ⊥), term γ := htarget
    _ = (algebraMap ℤ ℂ (n * bK) - algebraMap ℤ ℂ (n * bC)) -
          algebraMap ℤ ℂ (n * bNF) := by
            rw [hbK, hbC, hbNF]
    _ = algebraMap ℤ ℂ ((n * bK - n * bC) - n * bNF) := by
            simp [Int.cast_mul, Int.cast_sub]
    _ = algebraMap ℤ ℂ (n * (bK - bC - bNF)) := by
            congr 1
            ring

/-- Helper for Remark 11-11.1-3: the nontrivial ambient-character branch has a single owner.
Both the erased-quotient remainder step and the top-difference step should call this theorem
instead of rebuilding the kernel-growth recursion independently. -/
private theorem ambient_difference_pairing_divisible_of_nontrivial_character_by_kernel_growth
    (X : Finset (Subgroup G))
    (hXelem : ∀ H : Subgroup G, H ∈ X ↔ IsElementary H)
    {x : (H : X) → R(H.1)} {t : elementary_coherence_target X hXelem} {n : ℤ}
    (hdx : elementary_coherence_defect X hXelem x = n • t)
    (H : X)
    (sH : ((J : (Finset.univ : Finset (Subgroup H.1))) → R(J.1)) →ₗ[ℤ] R(H.1))
    (hsH : Function.LeftInverse sH
      (Representation.characterRingRestriction (Finset.univ : Finset (Subgroup H.1))).toLinearMap)
    (hproper :
      ∀ (J : Subgroup H.1) (hJ : J < ⊤) (α : J →* ℂˣ),
        let KX : X := ⟨J.map H.1.subtype,
          (hXelem (J.map H.1.subtype)).2 <|
            isElementary_of_mulEquiv_local
              (J.equivMapOfInjective H.1.subtype H.1.subtype_injective)
              (subgroup_isElementary_of_isElementary_local J ((hXelem H.1).1 H.2))⟩
        ∃ c : ℤ, linear_character_pairing_int H.1 J α (x KX) = n * c)
    (β : H.1 →* ℂˣ) (hβ : β ≠ 1) :
    let XH : Finset (Subgroup H.1) := Finset.univ
    let ψH : (J : XH) → R(J.1) := fun J ↦
      Subgroup.characterRingTransport
        (J.1.equivMapOfInjective H.1.subtype H.1.subtype_injective)
        (x ⟨J.1.map H.1.subtype,
          (hXelem (J.1.map H.1.subtype)).2 <|
            isElementary_of_mulEquiv_local
              (J.1.equivMapOfInjective H.1.subtype H.1.subtype_injective)
              (subgroup_isElementary_of_isElementary_local J.1 ((hXelem H.1).1 H.2))⟩)
    ∃ b : ℤ,
      ⟪((((β.toCharacterRing - 1 : R(H.1)) : H.1 → ℂ)),
          ((sH ψH : R(H.1)) : H.1 → ℂ)⟫ =
        algebraMap ℤ ℂ (n * b) := by
  classical
  dsimp
  let P : ℕ → Prop := fun m =>
    ∀ δ : H.1 →* ℂˣ, δ ≠ 1 → δ.ker.index = m →
      ∃ b : ℤ,
        ⟪((((δ.toCharacterRing - 1 : R(H.1)) : H.1 → ℂ)),
            ((sH
                (fun J ↦
                  Subgroup.characterRingTransport
                    (J.1.equivMapOfInjective H.1.subtype H.1.subtype_injective)
                    (x ⟨J.1.map H.1.subtype,
                      (hXelem (J.1.map H.1.subtype)).2 <|
                        isElementary_of_mulEquiv_local
                          (J.1.equivMapOfInjective H.1.subtype H.1.subtype_injective)
                          (subgroup_isElementary_of_isElementary_local J.1
                            ((hXelem H.1).1 H.2))⟩)) : R(H.1)) : H.1 → ℂ)⟫ =
          algebraMap ℤ ℂ (n * b)
  have hP : ∀ m : ℕ, P m := by
    intro m
    refine Nat.strong_induction_on m ?_
    intro m hm δ hδ hδindex
    -- Route correction: the strong-induction wrapper is now the sole owner of the measure
    -- bookkeeping; the kernel step theorem below should only do the source-faithful decomposition.
    have hstep :=
      ambient_difference_pairing_divisible_kernel_growth_step
        X hXelem hdx H sH hsH hproper δ hδ
        (fun ε hε hlt ↦
          hm ε.ker.index (by simpa [hδindex] using hlt) ε hε rfl)
    simpa [P] using hstep
  exact hP β.ker.index β hβ rfl

/-- Helper for Remark 11-11.1-3: once the quotient character induced by `β` is isolated, the
remaining erased quotient-character sum is the only arithmetic package still needed in the kernel
recursion. -/
private theorem erased_quotient_character_difference_divisible
    (X : Finset (Subgroup G))
    (hXelem : ∀ H : Subgroup G, H ∈ X ↔ IsElementary H)
    {x : (H : X) → R(H.1)} {t : elementary_coherence_target X hXelem} {n : ℤ}
    (hdx : elementary_coherence_defect X hXelem x = n • t)
    (H : X)
    (sH : ((J : (Finset.univ : Finset (Subgroup H.1))) → R(J.1)) →ₗ[ℤ] R(H.1))
    (hsH : Function.LeftInverse sH
      (Representation.characterRingRestriction (Finset.univ : Finset (Subgroup H.1))).toLinearMap)
    (hproper :
      ∀ (J : Subgroup H.1) (hJ : J < ⊤) (α : J →* ℂˣ),
        let KX : X := ⟨J.map H.1.subtype,
          (hXelem (J.map H.1.subtype)).2 <|
            isElementary_of_mulEquiv_local
              (J.equivMapOfInjective H.1.subtype H.1.subtype_injective)
              (subgroup_isElementary_of_isElementary_local J ((hXelem H.1).1 H.2))⟩
        ∃ c : ℤ, linear_character_pairing_int H.1 J α (x KX) = n * c)
    (β : H.1 →* ℂˣ)
    (γ : (H.1 ⧸ β.ker) →* ℂˣ)
    (hγ : γ ∈ Finset.univ.erase
      (QuotientGroup.lift β.ker β (show β.ker ≤ β.ker from le_rfl))) :
    ∃ bγ : ℤ,
      ⟪((((γ.comp (QuotientGroup.mk' β.ker)).toCharacterRing - 1 : R(H.1)) :
            H.1 → ℂ),
          ((sH
              (fun J ↦
                Subgroup.characterRingTransport
                  (J.1.equivMapOfInjective H.1.subtype H.1.subtype_injective)
                  (x ⟨J.1.map H.1.subtype,
                    (hXelem (J.1.map H.1.subtype)).2 <|
                      isElementary_of_mulEquiv_local
                        (J.1.equivMapOfInjective H.1.subtype H.1.subtype_injective)
                        (subgroup_isElementary_of_isElementary_local J.1
                          ((hXelem H.1).1 H.2))⟩)) : R(H.1)) : H.1 → ℂ)⟫ =
        algebraMap ℤ ℂ (n * bγ) := by
  classical
  -- Route correction: the kernel recursion must first produce a witness for a single erased
  -- quotient character. The finite-sum packaging is a separate step handled below.
  by_cases hδ : γ.comp (QuotientGroup.mk' β.ker) = 1
  · -- The trivial lifted character contributes the zero ambient difference term.
    exact
      erased_quotient_character_difference_divisible_of_comp_eq_one
        X hXelem H sH β γ hδ
  · let δ : H.1 →* ℂˣ := γ.comp (QuotientGroup.mk' β.ker)
    have hδ' : δ ≠ 1 := by
      simpa [δ] using hδ
    -- The nontrivial erased summand is now just the central ambient-character owner theorem.
    simpa [δ] using
      ambient_difference_pairing_divisible_of_nontrivial_character_by_kernel_growth
        X hXelem hdx H sH hsH hproper δ hδ'

/-- Helper for Remark 11-11.1-3: once the quotient character induced by `β` is isolated, the
remaining erased quotient-character sum is the only arithmetic package still needed in the kernel
recursion. -/
private theorem kernel_quotient_remainder_sum_divisible
    (X : Finset (Subgroup G))
    (hXelem : ∀ H : Subgroup G, H ∈ X ↔ IsElementary H)
    {x : (H : X) → R(H.1)} {t : elementary_coherence_target X hXelem} {n : ℤ}
    (hdx : elementary_coherence_defect X hXelem x = n • t)
    (H : X)
    (sH : ((J : (Finset.univ : Finset (Subgroup H.1))) → R(J.1)) →ₗ[ℤ] R(H.1))
    (hsH : Function.LeftInverse sH
      (Representation.characterRingRestriction (Finset.univ : Finset (Subgroup H.1))).toLinearMap)
    (hproper :
      ∀ (J : Subgroup H.1) (hJ : J < ⊤) (α : J →* ℂˣ),
        let KX : X := ⟨J.map H.1.subtype,
          (hXelem (J.map H.1.subtype)).2 <|
            isElementary_of_mulEquiv_local
              (J.equivMapOfInjective H.1.subtype H.1.subtype_injective)
              (subgroup_isElementary_of_isElementary_local J ((hXelem H.1).1 H.2))⟩
        ∃ c : ℤ, linear_character_pairing_int H.1 J α (x KX) = n * c)
    (β : H.1 →* ℂˣ) :
    let βq : (H.1 ⧸ β.ker) →* ℂˣ :=
      QuotientGroup.lift β.ker β (show β.ker ≤ β.ker from le_rfl)
    ∃ bΣ : ℤ,
      ∑ γ in Finset.univ.erase βq,
        ⟪((((γ.comp (QuotientGroup.mk' β.ker)).toCharacterRing - 1 : R(H.1)) :
              H.1 → ℂ),
            ((sH
                (fun J ↦
                  Subgroup.characterRingTransport
                    (J.1.equivMapOfInjective H.1.subtype H.1.subtype_injective)
                    (x ⟨J.1.map H.1.subtype,
                      (hXelem (J.1.map H.1.subtype)).2 <|
                        isElementary_of_mulEquiv_local
                          (J.1.equivMapOfInjective H.1.subtype H.1.subtype_injective)
                          (subgroup_isElementary_of_isElementary_local J.1
                            ((hXelem H.1).1 H.2))⟩)) : R(H.1)) : H.1 → ℂ)⟫ =
        algebraMap ℤ ℂ (n * bΣ) := by
  classical
  dsimp
  let term : ((H.1 ⧸ β.ker) →* ℂˣ) → ℂ := fun γ ↦
    ⟪((((γ.comp (QuotientGroup.mk' β.ker)).toCharacterRing - 1 : R(H.1)) :
          H.1 → ℂ),
        ((sH
            (fun J ↦
              Subgroup.characterRingTransport
                (J.1.equivMapOfInjective H.1.subtype H.1.subtype_injective)
                (x ⟨J.1.map H.1.subtype,
                  (hXelem (J.1.map H.1.subtype)).2 <|
                    isElementary_of_mulEquiv_local
                      (J.1.equivMapOfInjective H.1.subtype H.1.subtype_injective)
                      (subgroup_isElementary_of_isElementary_local J.1
                        ((hXelem H.1).1 H.2))⟩)) : R(H.1)) : H.1 → ℂ)⟫
  suffices hterm :
      ∀ γ ∈ Finset.univ.erase βq, ∃ bγ : ℤ, term γ = algebraMap ℤ ℂ (n * bγ) by
    obtain ⟨bΣ, hbΣ⟩ :=
      finset_sum_int_multiples (s := Finset.univ.erase βq) (f := term) (n := n) hterm
    refine ⟨bΣ, ?_⟩
    simpa [term] using hbΣ
  intro γ hγ
  -- The whole-sum statement is now only a packaging wrapper around the single-character witness.
  simpa [term, βq] using
    erased_quotient_character_difference_divisible
      X hXelem hdx H sH hsH hproper β γ hγ

/-- Helper for Remark 11-11.1-3: the nontrivial top-character branch should recurse on the proper
kernel of the transported ambient character, not on a false coatom identification of that kernel.
-/
private theorem top_difference_pairing_divisible_of_nontrivial_top_character_via_kernel_quotient_recursion
    (X : Finset (Subgroup G))
    (hXelem : ∀ H : Subgroup G, H ∈ X ↔ IsElementary H)
    {x : (H : X) → R(H.1)} {t : elementary_coherence_target X hXelem} {n : ℤ}
    (hdx : elementary_coherence_defect X hXelem x = n • t)
    (H : X)
    (sH : ((J : (Finset.univ : Finset (Subgroup H.1))) → R(J.1)) →ₗ[ℤ] R(H.1))
    (hsH : Function.LeftInverse sH
      (Representation.characterRingRestriction (Finset.univ : Finset (Subgroup H.1))).toLinearMap)
    (hproper :
      ∀ (J : Subgroup H.1) (hJ : J < ⊤) (α : J →* ℂˣ),
        let KX : X := ⟨J.map H.1.subtype,
          (hXelem (J.map H.1.subtype)).2 <|
            isElementary_of_mulEquiv_local
              (J.equivMapOfInjective H.1.subtype H.1.subtype_injective)
              (subgroup_isElementary_of_isElementary_local J ((hXelem H.1).1 H.2))⟩
        ∃ c : ℤ, linear_character_pairing_int H.1 J α (x KX) = n * c)
    (α : (⊤ : Subgroup H.1) →* ℂˣ) (hα : α ≠ 1) :
    let XH : Finset (Subgroup H.1) := Finset.univ
    let ψH : (J : XH) → R(J.1) := fun J ↦
      Subgroup.characterRingTransport
        (J.1.equivMapOfInjective H.1.subtype H.1.subtype_injective)
        (x ⟨J.1.map H.1.subtype,
          (hXelem (J.1.map H.1.subtype)).2 <|
            isElementary_of_mulEquiv_local
              (J.1.equivMapOfInjective H.1.subtype H.1.subtype_injective)
              (subgroup_isElementary_of_isElementary_local J.1 ((hXelem H.1).1 H.2))⟩)
    ∃ b : ℤ,
      ⟪((Subgroup.characterRingInduction (⊤ : Subgroup H.1)
            (α.toCharacterRing - 1) : R(H.1)) : H.1 → ℂ),
          ((sH ψH : R(H.1)) : H.1 → ℂ)⟫ =
        algebraMap ℤ ℂ (n * b) := by
  classical
  dsimp
  let β : H.1 →* ℂˣ := α.comp Subgroup.topEquiv.symm.toMonoidHom
  have hβ : β ≠ 1 := by
    intro hβone
    apply hα
    ext x
    -- Evaluate the ambient equality back on the top subgroup through `⊤ ≃ H`.
    simpa [β] using congrFun (congrArg MonoidHom.toFun hβone) x.1
  obtain ⟨b, hb⟩ :=
    ambient_difference_pairing_divisible_of_nontrivial_character_by_kernel_growth
      X hXelem hdx H sH hsH hproper β hβ
  refine ⟨b, ?_⟩
  -- The top-character statement is just the ambient-difference statement transported through
  -- the canonical equivalence `⊤ ≃ H`.
  calc
    ⟪((Subgroup.characterRingInduction (⊤ : Subgroup H.1)
          (α.toCharacterRing - 1) : R(H.1)) : H.1 → ℂ),
        ((sH ψH : R(H.1)) : H.1 → ℂ)⟫ =
      ⟪((((β.toCharacterRing - 1 : R(H.1)) : H.1 → ℂ)),
          ((sH ψH : R(H.1)) : H.1 → ℂ)⟫ := by
            exact
              (ambient_difference_pairing_eq_top_induced_difference_pairing
                (ξ := sH ψH) α).symm
    _ = algebraMap ℤ ℂ (n * b) := hb

/-- Helper for Remark 11-11.1-3: isolate the coatom quotient package before the ambient theorem
consumes it to rebuild the actual top local pairing. This keeps the source-faithful quotient step
available without forcing a forward reference. -/
private theorem coatom_quotient_pairing_divisible_package_core_of_proper_branch
    (X : Finset (Subgroup G))
    (hXelem : ∀ H : Subgroup G, H ∈ X ↔ IsElementary H)
    (s : ((H : X) → R(H.1)) →ₗ[ℤ] R(G))
    (hs : Function.LeftInverse s (Representation.characterRingRestriction X).toLinearMap)
    {x : (H : X) → R(H.1)} {t : elementary_coherence_target X hXelem} {n : ℤ}
    (hn : n ≠ 0) (hx : s x = 0)
    (hdx : elementary_coherence_defect X hXelem x = n • t)
    (H : X)
    (sH : ((J : (Finset.univ : Finset (Subgroup H.1))) → R(J.1)) →ₗ[ℤ] R(H.1))
    (hsH : Function.LeftInverse sH
      (Representation.characterRingRestriction (Finset.univ : Finset (Subgroup H.1))).toLinearMap)
    (hproper :
      ∀ (J : Subgroup H.1) (hJ : J < ⊤) (α : J →* ℂˣ),
        let KX : X := ⟨J.map H.1.subtype,
          (hXelem (J.map H.1.subtype)).2 <|
            isElementary_of_mulEquiv_local
              (J.equivMapOfInjective H.1.subtype H.1.subtype_injective)
              (subgroup_isElementary_of_isElementary_local J ((hXelem H.1).1 H.2))⟩
        ∃ c : ℤ, linear_character_pairing_int H.1 J α (x KX) = n * c) :
    let XH : Finset (Subgroup H.1) := Finset.univ
    let ψH : (J : XH) → R(J.1) := fun J ↦
      Subgroup.characterRingTransport
        (J.1.equivMapOfInjective H.1.subtype H.1.subtype_injective)
        (x ⟨J.1.map H.1.subtype,
          (hXelem (J.1.map H.1.subtype)).2 <|
            isElementary_of_mulEquiv_local
              (J.1.equivMapOfInjective H.1.subtype H.1.subtype_injective)
              (subgroup_isElementary_of_isElementary_local J.1 ((hXelem H.1).1 H.2))⟩)
    let ξH : R(H.1) := sH ψH
    (∃ b₀ : ℤ, ⟪((1 : R(H.1)) : H.1 → ℂ), (ξH : H.1 → ℂ)⟫ = algebraMap ℤ ℂ (n * b₀)) ∧
      ∀ α : (⊤ : Subgroup H.1) →* ℂˣ,
        ∃ b : ℤ,
          ⟪((Subgroup.characterRingInduction (⊤ : Subgroup H.1)
                (α.toCharacterRing - 1) : R(H.1)) : H.1 → ℂ),
              (ξH : H.1 → ℂ)⟫ =
            algebraMap ℤ ℂ (n * b) := by
  classical
  -- Route correction: isolate the quotient package before rebuilding the actual top coordinate
  -- pairing. The ambient theorem should consume this package through the already-proved
  -- trivial-line plus top-difference recombination lemma.
  dsimp
  by_cases htrivial : (⊥ : Subgroup H.1) = ⊤
  · have htrivial_blocker :
        (∃ b₀ : ℤ, ⟪((1 : R(H.1)) : H.1 → ℂ), ((sH ψH : R(H.1)) : H.1 → ℂ)⟫ =
            algebraMap ℤ ℂ (n * b₀)) ∧
          ∀ α : (⊤ : Subgroup H.1) →* ℂˣ,
            ∃ b : ℤ,
              ⟪((Subgroup.characterRingInduction (⊤ : Subgroup H.1)
                    (α.toCharacterRing - 1) : R(H.1)) : H.1 → ℂ),
                  ((sH ψH : R(H.1)) : H.1 → ℂ)⟫ =
                algebraMap ℤ ℂ (n * b) := by
      refine ⟨?_, ?_⟩
      · -- The trivial branch now closes through the repaired residual-family bridge.
        exact
          local_trivial_coordinate_pairing_divisible_of_defect_multiple
            X hXelem s hs hn hx hdx H sH hsH htrivial
      · intro α
        refine ⟨0, ?_⟩
        -- On the trivial ambient group every top character is `1`, so the difference term vanishes.
        rw [top_induced_difference_eq_zero_of_bot_eq_top_local htrivial α]
        simp
    exact htrivial_blocker
  · obtain ⟨M, hM, hbotM⟩ :=
      (eq_top_or_exists_le_coatom (⊥ : Subgroup H.1)).resolve_left htrivial
    letI : Group.IsNilpotent H.1 := by
      rcases (hXelem H.1).1 H.2 with ⟨p, hp⟩
      exact IsPElementary.isNilpotent hp
    letI : M.Normal :=
      Subgroup.NormalizerCondition.normal_of_coatom
        (G := H.1) (H := M) (normalizerCondition_of_isNilpotent (G := H.1)) hM
    letI : IsSimpleGroup (H.1 ⧸ M) :=
      isSimpleGroup_quotient_of_isCoatom (G := H.1) M hM
    let hcomm : ∀ a b : H.1 ⧸ M, a * b = b * a :=
      IsSimpleGroup.comm_iff_isSolvable.mpr inferInstance
    letI : CommGroup (H.1 ⧸ M) :=
      { QuotientGroup.Quotient.group M with
        mul_comm := hcomm }
    letI : Fintype ((H.1 ⧸ M) →* ℂˣ) := linearCharacterFintype
    have hMproper : M < ⊤ := hM.lt_top
    have hMpair :
        ∃ bM : ℤ,
          ⟪(Subgroup.characterRingInduction M (1 : R(M)) : H.1 → ℂ),
              ((sH ψH : R(H.1)) : H.1 → ℂ)⟫ =
            algebraMap ℤ ℂ (n * bM) := by
      simpa using
        proper_induced_pairing_divisible_of_transport_pairing_int_divisible
          X hXelem hdx H sH hsH M (1 : M →* ℂˣ) (hproper M hMproper (1 : M →* ℂˣ))
    have hcoatom_blocker :
        (∃ b₀ : ℤ, ⟪((1 : R(H.1)) : H.1 → ℂ), ((sH ψH : R(H.1)) : H.1 → ℂ)⟫ =
            algebraMap ℤ ℂ (n * b₀)) ∧
          ∀ α : (⊤ : Subgroup H.1) →* ℂˣ,
            ∃ b : ℤ,
              ⟪((Subgroup.characterRingInduction (⊤ : Subgroup H.1)
                    (α.toCharacterRing - 1) : R(H.1)) : H.1 → ℂ),
                  ((sH ψH : R(H.1)) : H.1 → ℂ)⟫ =
                algebraMap ℤ ℂ (n * b) := by
      -- TODO: pair
      -- `induced_trivial_pairing_eq_index_trivial_pairing_add_quotient_difference_sum`
      -- against `ξH = sH ψH`, use `hMpair` for the coatom term, and rewrite the quotient sum via
      -- `top_induced_difference_eq_ambient_difference` together with
      -- `prime_card_quotient_of_isCoatom_of_isElementary`.
      have hprime :
          (Nat.card (H.1 ⧸ M)).Prime :=
        prime_card_quotient_of_isCoatom_of_isElementary M hM ((hXelem H.1).1 H.2)
      have hpair_rewrite :
          ⟪(Subgroup.characterRingInduction M (1 : R(M)) : H.1 → ℂ), ((sH ψH : R(H.1)) : H.1 → ℂ)⟫ =
            (M.index : ℂ) * ⟪((1 : R(H.1)) : H.1 → ℂ), ((sH ψH : R(H.1)) : H.1 → ℂ)⟫ +
              ∑ β : (H.1 ⧸ M) →* ℂˣ,
                ⟪((((β.comp (QuotientGroup.mk' M)).toCharacterRing - 1 : R(H.1)) : H.1 → ℂ),
                    ((sH ψH : R(H.1)) : H.1 → ℂ)⟫ := by
        simpa using
          induced_trivial_pairing_eq_index_trivial_pairing_add_quotient_difference_sum
            (M := M) hcomm (ξ := sH ψH)
      have hquotdiff :
          ∀ β : (H.1 ⧸ M) →* ℂˣ,
            ∃ bβ : ℤ,
              ⟪((((β.comp (QuotientGroup.mk' M)).toCharacterRing - 1 : R(H.1)) : H.1 → ℂ),
                  ((sH ψH : R(H.1)) : H.1 → ℂ)⟫ =
                algebraMap ℤ ℂ (n * bβ) := by
        intro β
        let α : (⊤ : Subgroup H.1) →* ℂˣ :=
          (β.comp (QuotientGroup.mk' M)).comp Subgroup.topEquiv.symm.toMonoidHom
        by_cases hα : α = 1
        · refine ⟨0, ?_⟩
          have hambient_zero :
              (((β.comp (QuotientGroup.mk' M)).toCharacterRing - 1 : R(H.1))) = 0 := by
            calc
              (((β.comp (QuotientGroup.mk' M)).toCharacterRing - 1 : R(H.1))) =
                  Subgroup.characterRingInduction (⊤ : Subgroup H.1) (α.toCharacterRing - 1) := by
                    symm
                    simpa [α] using
                      top_induced_difference_eq_ambient_difference (H0 := H.1) α
              _ = 0 := by
                    rw [hα]
                    simp
          simp [hambient_zero]
        · rcases
            top_difference_pairing_divisible_of_nontrivial_top_character_via_kernel_quotient_recursion
              X hXelem hdx H sH hsH hproper α hα with
            ⟨bβ, hbβ⟩
          refine ⟨bβ, ?_⟩
          calc
            ⟪((((β.comp (QuotientGroup.mk' M)).toCharacterRing - 1 : R(H.1)) : H.1 → ℂ),
                ((sH ψH : R(H.1)) : H.1 → ℂ)⟫ =
              ⟪((Subgroup.characterRingInduction (⊤ : Subgroup H.1)
                    (α.toCharacterRing - 1) : R(H.1)) : H.1 → ℂ),
                  ((sH ψH : R(H.1)) : H.1 → ℂ)⟫ := by
                    simpa [α] using
                      ambient_difference_pairing_eq_top_induced_difference_pairing
                        (ξ := sH ψH) α
            _ = algebraMap ℤ ℂ (n * bβ) := hbβ
      have htopdiff :
          ∀ α : (⊤ : Subgroup H.1) →* ℂˣ, α ≠ 1 →
            ∃ b : ℤ,
              ⟪((Subgroup.characterRingInduction (⊤ : Subgroup H.1)
                    (α.toCharacterRing - 1) : R(H.1)) : H.1 → ℂ),
                  ((sH ψH : R(H.1)) : H.1 → ℂ)⟫ =
                algebraMap ℤ ℂ (n * b) := by
        intro α hα
        -- Route correction: `ker β` is only guaranteed to be proper here, not a coatom.
        -- The next source-faithful step is therefore to recurse on that proper subgroup and then
        -- reassemble the ambient top-difference pairing, rather than forcing a false coatom claim
        -- for the kernel itself.
        exact
          top_difference_pairing_divisible_of_nontrivial_top_character_via_kernel_quotient_recursion
            X hXelem hdx H sH hsH hproper α hα
      have hfixed_coatom :
          (∃ b₀ : ℤ,
            (M.index : ℂ) * ⟪((1 : R(H.1)) : H.1 → ℂ), ((sH ψH : R(H.1)) : H.1 → ℂ)⟫ =
              algebraMap ℤ ℂ (n * b₀)) ∧
            ∀ α : (⊤ : Subgroup H.1) →* ℂˣ,
              ∃ b : ℤ,
                ⟪((Subgroup.characterRingInduction (⊤ : Subgroup H.1)
                      (α.toCharacterRing - 1) : R(H.1)) : H.1 → ℂ),
                    ((sH ψH : R(H.1)) : H.1 → ℂ)⟫ =
                  algebraMap ℤ ℂ (n * b) := by
        exact
          coatom_top_local_pairing_divisible_package_of_fixed_coatom
            M hcomm (sH ψH) hMpair hpair_rewrite hquotdiff htopdiff hprime
      refine ⟨?_, hfixed_coatom.2⟩
      -- The unscaled trivial-line witness comes from the ambient residual-family factorization,
      -- not from the fixed-coatom arithmetic package.
      exact
        top_local_trivial_pairing_divisible_of_residual_family
          X hXelem s hs hn hx hdx H sH hsH
    exact hcoatom_blocker

/-- Helper for Remark 11-11.1-3: if `J ≤ M ≤ H` and `J.subgroupOf M = ⊤`, then the `X`-indexed
ambient coordinates cut out by `J` and by `M` are the same. -/
private theorem subgroup_chain_coordinate_eq_of_subgroupOf_eq_top_local
    (X : Finset (Subgroup G))
    (hXelem : ∀ H : Subgroup G, H ∈ X ↔ IsElementary H)
    (H : X) (M J : Subgroup H.1) (hJM : J ≤ M)
    (hJtop : J.subgroupOf M = ⊤) :
    (⟨J.map H.1.subtype,
      (hXelem (J.map H.1.subtype)).2 <|
        isElementary_of_mulEquiv_local
          (J.equivMapOfInjective H.1.subtype H.1.subtype_injective)
          (subgroup_isElementary_of_isElementary_local J ((hXelem H.1).1 H.2))⟩ : X) =
      ⟨M.map H.1.subtype,
        (hXelem (M.map H.1.subtype)).2 <|
          isElementary_of_mulEquiv_local
            (M.equivMapOfInjective H.1.subtype H.1.subtype_injective)
            (subgroup_isElementary_of_isElementary_local M ((hXelem H.1).1 H.2))⟩ := by
  have hJM_eq : J = M := subgroup_eq_of_le_of_subgroupOf_eq_top_local M J hJM hJtop
  -- Once `J = M`, the two ambient `X`-coordinates are definitionally the same mapped subgroup.
  apply Subtype.ext
  simp [hJM_eq]

/-- Helper for Remark 11-11.1-3: the proper-subgroup branch should choose a coatom above `J`,
recurse on the smaller ambient subgroup, and then transport the witness back along the subgroup
chain `J ≤ M ≤ H`. -/
private theorem proper_branch_from_smaller_ambient_package
    (X : Finset (Subgroup G))
    (hXelem : ∀ H : Subgroup G, H ∈ X ↔ IsElementary H)
    {x : (H : X) → R(H.1)} {n : ℤ}
    (H : X) (M : Subgroup H.1) (J : Subgroup M) (α : J →* ℂˣ)
    (hproperM :
      ∀ (L : Subgroup M) (hL : L < ⊤) (χ : L →* ℂˣ),
        let KX : X := ⟨(L.map M.subtype).map H.1.subtype,
          (hXelem ((L.map M.subtype).map H.1.subtype)).2 <|
            isElementary_of_mulEquiv_local
              ((L.map M.subtype).equivMapOfInjective H.1.subtype H.1.subtype_injective)
              (subgroup_isElementary_of_isElementary_local (L.map M.subtype)
                (isElementary_of_mulEquiv_local
                  (M.equivMapOfInjective H.1.subtype H.1.subtype_injective)
                  (subgroup_isElementary_of_isElementary_local M ((hXelem H.1).1 H.2))))⟩
        ∃ c : ℤ,
          linear_character_pairing_int M L χ
            (Subgroup.characterRingTransport
              ((L.map M.subtype).equivMapOfInjective H.1.subtype H.1.subtype_injective)
              (x KX)) =
            n * c)
    (htopM :
      ∀ χ : M →* ℂˣ,
        let MX : X := ⟨M.map H.1.subtype,
          (hXelem (M.map H.1.subtype)).2 <|
            isElementary_of_mulEquiv_local
              (M.equivMapOfInjective H.1.subtype H.1.subtype_injective)
              (subgroup_isElementary_of_isElementary_local M ((hXelem H.1).1 H.2))⟩
        ∃ b : ℤ,
          ⟪(χ.toCharacterRing : M → ℂ),
              ((Subgroup.characterRingTransport
                (M.equivMapOfInjective H.1.subtype H.1.subtype_injective)
                (x MX) : R(M)) : M → ℂ)⟫ =
            algebraMap ℤ ℂ (n * b)) :
    let KX : X := ⟨(J.map M.subtype).map H.1.subtype,
      (hXelem ((J.map M.subtype).map H.1.subtype)).2 <|
        isElementary_of_mulEquiv_local
          ((J.map M.subtype).equivMapOfInjective H.1.subtype H.1.subtype_injective)
          (subgroup_isElementary_of_isElementary_local (J.map M.subtype)
            (isElementary_of_mulEquiv_local
              (M.equivMapOfInjective H.1.subtype H.1.subtype_injective)
              (subgroup_isElementary_of_isElementary_local M ((hXelem H.1).1 H.2))))⟩
    ∃ c : ℤ,
      linear_character_pairing_int H.1 (J.map M.subtype) (mapped_linear_character_local M J α)
        (x KX) =
        n * c := by
  classical
  let MX : X := ⟨M.map H.1.subtype,
    (hXelem (M.map H.1.subtype)).2 <|
      isElementary_of_mulEquiv_local
        (M.equivMapOfInjective H.1.subtype H.1.subtype_injective)
        (subgroup_isElementary_of_isElementary_local M ((hXelem H.1).1 H.2))⟩
  let KX : X := ⟨(J.map M.subtype).map H.1.subtype,
    (hXelem ((J.map M.subtype).map H.1.subtype)).2 <|
      isElementary_of_mulEquiv_local
        ((J.map M.subtype).equivMapOfInjective H.1.subtype H.1.subtype_injective)
        (subgroup_isElementary_of_isElementary_local (J.map M.subtype)
          (isElementary_of_mulEquiv_local
            (M.equivMapOfInjective H.1.subtype H.1.subtype_injective)
            (subgroup_isElementary_of_isElementary_local M ((hXelem H.1).1 H.2))))⟩
  change ∃ c : ℤ,
      linear_character_pairing_int H.1 (J.map M.subtype) (mapped_linear_character_local M J α)
        (x KX) =
        n * c
  by_cases hJtop : J = ⊤
  · -- When `J = ⊤` inside `M`, the smaller-ambient top package already gives the witness.
    subst hJtop
    have htop := htopM α
    dsimp [MX, KX] at htop ⊢
    rcases htop with ⟨b, hb⟩
    refine ⟨b, ?_⟩
    apply Int.cast_injective
    -- Read the ambient integer pairing back through the transported top coordinate of `M`.
    calc
      algebraMap ℤ ℂ (linear_character_pairing_int H.1 M α (x MX)) =
          ⟪(α.toCharacterRing : M → ℂ),
              ((Subgroup.characterRingTransport
                (M.equivMapOfInjective H.1.subtype H.1.subtype_injective)
                (x MX) : R(M)) : M → ℂ)⟫ := by
                  simpa using
                    (subgroup_linear_character_pairing_int_transport_eq H.1 M α (x MX)).symm
      _ = algebraMap ℤ ℂ (n * b) := hb
  · -- On the proper branch, reuse the smaller-ambient witness and transport it up the chain.
    have hJproper : J < ⊤ := lt_top_iff_ne_top.mpr hJtop
    have hproper := hproperM J hJproper α
    dsimp [KX] at hproper
    simpa [KX] using
      subgroup_chain_pairing_divisible_transport_local H.1 M J α (x KX) hproper

/-- Helper for Remark 11-11.1-3: once a coatom `M` above `J` is chosen, the remaining proper
branch step is purely a transport argument. The smaller-ambient proper package handles
`J.subgroupOf M < ⊤`, and the smaller-ambient top witness handles `J.subgroupOf M = ⊤`. -/
private theorem coatom_cover_step_for_hproper_all
    (X : Finset (Subgroup G))
    (hXelem : ∀ H : Subgroup G, H ∈ X ↔ IsElementary H)
    (s : ((H : X) → R(H.1)) →ₗ[ℤ] R(G))
    (hs : Function.LeftInverse s (Representation.characterRingRestriction X).toLinearMap)
    {x : (H : X) → R(H.1)} {t : elementary_coherence_target X hXelem} {n : ℤ}
    (hn : n ≠ 0) (hx : s x = 0)
    (hdx : elementary_coherence_defect X hXelem x = n • t)
    (H : X)
    (sH : ((J : (Finset.univ : Finset (Subgroup H.1))) → R(J.1)) →ₗ[ℤ] R(H.1))
    (hsH : Function.LeftInverse sH
      (Representation.characterRingRestriction (Finset.univ : Finset (Subgroup H.1))).toLinearMap)
    (M J : Subgroup H.1) (_hJ : J < ⊤) (hJM : J ≤ M) (α : J →* ℂˣ)
    (hproperM :
      ∀ (L : Subgroup M) (hL : L < ⊤) (χ : L →* ℂˣ),
        let KX : X := ⟨(L.map M.subtype).map H.1.subtype,
          (hXelem ((L.map M.subtype).map H.1.subtype)).2 <|
            isElementary_of_mulEquiv_local
              ((L.map M.subtype).equivMapOfInjective H.1.subtype H.1.subtype_injective)
              (subgroup_isElementary_of_isElementary_local (L.map M.subtype)
                (isElementary_of_mulEquiv_local
                  (M.equivMapOfInjective H.1.subtype H.1.subtype_injective)
                  (subgroup_isElementary_of_isElementary_local M ((hXelem H.1).1 H.2))))⟩
        ∃ c : ℤ,
          linear_character_pairing_int M L χ
            (Subgroup.characterRingTransport
              ((L.map M.subtype).equivMapOfInjective H.1.subtype H.1.subtype_injective)
              (x KX)) =
            n * c)
    (htopM :
      ∀ χ : M →* ℂˣ,
        let MX : X := ⟨M.map H.1.subtype,
          (hXelem (M.map H.1.subtype)).2 <|
            isElementary_of_mulEquiv_local
              (M.equivMapOfInjective H.1.subtype H.1.subtype_injective)
              (subgroup_isElementary_of_isElementary_local M ((hXelem H.1).1 H.2))⟩
        ∃ b : ℤ,
          ⟪(χ.toCharacterRing : M → ℂ),
              ((Subgroup.characterRingTransport
                (M.equivMapOfInjective H.1.subtype H.1.subtype_injective)
                (x MX) : R(M)) : M → ℂ)⟫ =
            algebraMap ℤ ℂ (n * b)) :
    let KX : X := ⟨J.map H.1.subtype,
      (hXelem (J.map H.1.subtype)).2 <|
        isElementary_of_mulEquiv_local
          (J.equivMapOfInjective H.1.subtype H.1.subtype_injective)
          (subgroup_isElementary_of_isElementary_local J ((hXelem H.1).1 H.2))⟩
    ∃ c : ℤ, linear_character_pairing_int H.1 J α (x KX) = n * c := by
  classical
  let MX : X := ⟨M.map H.1.subtype,
    (hXelem (M.map H.1.subtype)).2 <|
      isElementary_of_mulEquiv_local
        (M.equivMapOfInjective H.1.subtype H.1.subtype_injective)
        (subgroup_isElementary_of_isElementary_local M ((hXelem H.1).1 H.2))⟩
  let KX : X := ⟨J.map H.1.subtype,
    (hXelem (J.map H.1.subtype)).2 <|
      isElementary_of_mulEquiv_local
        (J.equivMapOfInjective H.1.subtype H.1.subtype_injective)
        (subgroup_isElementary_of_isElementary_local J ((hXelem H.1).1 H.2))⟩
  change ∃ c : ℤ, linear_character_pairing_int H.1 J α (x KX) = n * c
  by_cases hJtop : J.subgroupOf M = ⊤
  · have hJM_eq : J = M := subgroup_eq_of_le_of_subgroupOf_eq_top_local M J hJM hJtop
    subst hJM_eq
    have htop_current :
        let XH : Finset (Subgroup H.1) := Finset.univ
        let ψH : (J : XH) → R(J.1) := fun J ↦
          Subgroup.characterRingTransport
            (J.1.equivMapOfInjective H.1.subtype H.1.subtype_injective)
            (x ⟨J.1.map H.1.subtype,
              (hXelem (J.1.map H.1.subtype)).2 <|
                isElementary_of_mulEquiv_local
                  (J.1.equivMapOfInjective H.1.subtype H.1.subtype_injective)
                  (subgroup_isElementary_of_isElementary_local J.1 ((hXelem H.1).1 H.2))⟩)
        let K0 : XH := ⟨M, by simp [XH]⟩
        ∃ b : ℤ,
          ⟪(α.toCharacterRing : M → ℂ),
              (((Representation.characterRingRestriction XH) (sH ψH) K0 : R(M)) : M → ℂ)⟫ =
            algebraMap ℤ ℂ (n * b) := by
      dsimp
      rcases htopM α with ⟨b, hb⟩
      refine ⟨b, ?_⟩
      have hcoord :
          ((Representation.characterRingRestriction
              (Finset.univ : Finset (Subgroup H.1)))
              (sH
                (fun J ↦
                  Subgroup.characterRingTransport
                    (J.1.equivMapOfInjective H.1.subtype H.1.subtype_injective)
                    (x ⟨J.1.map H.1.subtype,
                      (hXelem (J.1.map H.1.subtype)).2 <|
                        isElementary_of_mulEquiv_local
                          (J.1.equivMapOfInjective H.1.subtype H.1.subtype_injective)
                          (subgroup_isElementary_of_isElementary_local J.1
                            ((hXelem H.1).1 H.2))⟩))
              ⟨M, by simp⟩ : R(M)) =
            Subgroup.characterRingTransport
              (M.equivMapOfInjective H.1.subtype H.1.subtype_injective)
              (x MX) := by
        exact congrFun
          (hsH
            (fun J ↦
              Subgroup.characterRingTransport
                (J.1.equivMapOfInjective H.1.subtype H.1.subtype_injective)
                (x ⟨J.1.map H.1.subtype,
                  (hXelem (J.1.map H.1.subtype)).2 <|
                    isElementary_of_mulEquiv_local
                      (J.1.equivMapOfInjective H.1.subtype H.1.subtype_injective)
                      (subgroup_isElementary_of_isElementary_local J.1
                        ((hXelem H.1).1 H.2))⟩))) ⟨M, by simp⟩
      rw [hcoord]
      simpa [MX] using hb
    simpa [MX, KX] using
      residual_subgroup_pairing_int_divisible_of_given_top_local_pairing
        X hXelem s hs hn hx hdx H sH hsH M α htop_current
  · let αM : J.subgroupOf M →* ℂˣ :=
      α.comp (Subgroup.subgroupOfEquivOfLe hJM).toMonoidHom
    have hJproper : J.subgroupOf M < ⊤ := lt_top_iff_ne_top.mpr hJtop
    have hstep :=
      proper_branch_from_smaller_ambient_package
        X hXelem H M (J.subgroupOf M) αM hproperM htopM
    -- Reidentify the subgroup cut out inside `M` with the original `J`, then collapse the
    -- transported character back to `α`.
    simpa [KX, MX, αM, subgroup_chain_map_subgroupOf_eq_local (G := H.1) M J hJM] using hstep

/-- Helper for Remark 11-11.1-3: the ambient coatom recursion is owned by a single package theorem.
It must recurse on smaller ambient elementary subgroups while keeping both the proper-subgroup
pairings and the top-local pairings available for transport back to the original ambient group. -/
private theorem ambient_local_pairing_divisibility_package_strong_induction
    (X : Finset (Subgroup G))
    (hXelem : ∀ H : Subgroup G, H ∈ X ↔ IsElementary H)
    (s : ((H : X) → R(H.1)) →ₗ[ℤ] R(G))
    (hs : Function.LeftInverse s (Representation.characterRingRestriction X).toLinearMap)
    {x : (H : X) → R(H.1)} {t : elementary_coherence_target X hXelem} {n : ℤ}
    (hn : n ≠ 0) (hx : s x = 0)
    (hdx : elementary_coherence_defect X hXelem x = n • t)
    (H : X)
    (sH : ((J : (Finset.univ : Finset (Subgroup H.1))) → R(J.1)) →ₗ[ℤ] R(H.1))
    (hsH : Function.LeftInverse sH
      (Representation.characterRingRestriction (Finset.univ : Finset (Subgroup H.1))).toLinearMap) :
    (∀ (J : Subgroup H.1) (hJ : J < ⊤) (α : J →* ℂˣ),
      let KX : X := ⟨J.map H.1.subtype,
        (hXelem (J.map H.1.subtype)).2 <|
          isElementary_of_mulEquiv_local
            (J.equivMapOfInjective H.1.subtype H.1.subtype_injective)
            (subgroup_isElementary_of_isElementary_local J ((hXelem H.1).1 H.2))⟩
      ∃ c : ℤ, linear_character_pairing_int H.1 J α (x KX) = n * c) ∧
      (∀ α : (⊤ : Subgroup H.1) →* ℂˣ,
        let XH : Finset (Subgroup H.1) := Finset.univ
        let ψH : (J : XH) → R(J.1) := fun J ↦
          Subgroup.characterRingTransport
            (J.1.equivMapOfInjective H.1.subtype H.1.subtype_injective)
            (x ⟨J.1.map H.1.subtype,
              (hXelem (J.1.map H.1.subtype)).2 <|
                isElementary_of_mulEquiv_local
                  (J.1.equivMapOfInjective H.1.subtype H.1.subtype_injective)
                  (subgroup_isElementary_of_isElementary_local J.1 ((hXelem H.1).1 H.2))⟩)
      let K0 : XH := ⟨⊤, by simp [XH]⟩
      ∃ b : ℤ,
          ⟪(α.toCharacterRing : (⊤ : Subgroup H.1) → ℂ),
            (((Representation.characterRingRestriction XH) (sH ψH) K0 : R((⊤ : Subgroup H.1))) :
                (⊤ : Subgroup H.1) → ℂ)⟫ =
            algebraMap ℤ ℂ (n * b)) := by
  classical
  -- Route correction: the coatom step needs the full smaller-ambient package, not only the
  -- proper-subgroup projection. This theorem is therefore the single owner of the ambient
  -- recursion, and later lemmas should only project from it.
  let P : ℕ → Prop := fun m ↦
    ∀ (H : X), Nat.card H.1 = m →
      ∀ (sH : ((J : (Finset.univ : Finset (Subgroup H.1))) → R(J.1)) →ₗ[ℤ] R(H.1))
        (hsH : Function.LeftInverse sH
          (Representation.characterRingRestriction
            (Finset.univ : Finset (Subgroup H.1))).toLinearMap),
        (∀ (J : Subgroup H.1) (hJ : J < ⊤) (α : J →* ℂˣ),
          let KX : X := ⟨J.map H.1.subtype,
            (hXelem (J.map H.1.subtype)).2 <|
              isElementary_of_mulEquiv_local
                (J.equivMapOfInjective H.1.subtype H.1.subtype_injective)
                (subgroup_isElementary_of_isElementary_local J ((hXelem H.1).1 H.2))⟩
          ∃ c : ℤ, linear_character_pairing_int H.1 J α (x KX) = n * c) ∧
          (∀ α : (⊤ : Subgroup H.1) →* ℂˣ,
            let XH : Finset (Subgroup H.1) := Finset.univ
            let ψH : (J : XH) → R(J.1) := fun J ↦
              Subgroup.characterRingTransport
                (J.1.equivMapOfInjective H.1.subtype H.1.subtype_injective)
                (x ⟨J.1.map H.1.subtype,
                  (hXelem (J.1.map H.1.subtype)).2 <|
                    isElementary_of_mulEquiv_local
                      (J.1.equivMapOfInjective H.1.subtype H.1.subtype_injective)
                      (subgroup_isElementary_of_isElementary_local J.1
                        ((hXelem H.1).1 H.2))⟩)
            let K0 : XH := ⟨⊤, by simp [XH]⟩
            ∃ b : ℤ,
              ⟪(α.toCharacterRing : (⊤ : Subgroup H.1) → ℂ),
                (((Representation.characterRingRestriction XH) (sH ψH) K0 :
                    R((⊤ : Subgroup H.1))) : (⊤ : Subgroup H.1) → ℂ)⟫ =
                algebraMap ℤ ℂ (n * b))
  have hP : ∀ m, (∀ k < m, P k) → P m := by
    intro m ih H hcard sH hsH
    have hproper_all :
        ∀ (J : Subgroup H.1) (hJ : J < ⊤) (α : J →* ℂˣ),
          let KX : X := ⟨J.map H.1.subtype,
            (hXelem (J.map H.1.subtype)).2 <|
              isElementary_of_mulEquiv_local
                (J.equivMapOfInjective H.1.subtype H.1.subtype_injective)
                (subgroup_isElementary_of_isElementary_local J ((hXelem H.1).1 H.2))⟩
          ∃ c : ℤ, linear_character_pairing_int H.1 J α (x KX) = n * c := by
      intro J hJ α
      obtain ⟨M, hM, hJM⟩ :=
        (eq_top_or_exists_le_coatom J).resolve_left hJ.ne
      let MX : X := ⟨M.map H.1.subtype,
        (hXelem (M.map H.1.subtype)).2 <|
          isElementary_of_mulEquiv_local
            (M.equivMapOfInjective H.1.subtype H.1.subtype_injective)
            (subgroup_isElementary_of_isElementary_local M ((hXelem H.1).1 H.2))⟩
      obtain ⟨sM, hsM⟩ :=
        characterRingRestriction_has_leftInverse_of_detection_by_restrictions
          (G := M) (Finset.univ : Finset (Subgroup M))
          subgroup_restriction_detection_on_elementary_group
      have hcardM : Nat.card M < m := by
        rw [← hcard]
        exact coatom_card_lt_ambient_local H.1 M hM
      have hMXcard : Nat.card MX.1 = Nat.card M := by
        dsimp [MX]
        simpa using subgroup_chain_map_card_eq_local H.1 M
      have hrec := ih (Nat.card M) hcardM MX hMXcard sM hsM
      have hproperM :
          ∀ (L : Subgroup M) (hL : L < ⊤) (χ : L →* ℂˣ),
            let KX : X := ⟨(L.map M.subtype).map H.1.subtype,
              (hXelem ((L.map M.subtype).map H.1.subtype)).2 <|
                isElementary_of_mulEquiv_local
                  ((L.map M.subtype).equivMapOfInjective H.1.subtype
                    H.1.subtype_injective)
                  (subgroup_isElementary_of_isElementary_local (L.map M.subtype)
                    (isElementary_of_mulEquiv_local
                      (M.equivMapOfInjective H.1.subtype H.1.subtype_injective)
                      (subgroup_isElementary_of_isElementary_local M
                        ((hXelem H.1).1 H.2))))⟩
            ∃ c : ℤ,
              linear_character_pairing_int M L χ
                (Subgroup.characterRingTransport
                  ((L.map M.subtype).equivMapOfInjective H.1.subtype
                    H.1.subtype_injective)
                  (x KX)) =
                n * c := by
        intro L hL χ
        let LX : Subgroup MX.1 := L.map M.subtype
        have hLXproper : LX < ⊤ := by
          refine lt_top_iff_ne_top.mpr ?_
          intro hLXtop
          have hlt :
              Nat.card LX < Nat.card MX.1 := by
            dsimp [LX, MX]
            rw [subgroup_chain_map_card_eq_local H.1 M, subgroup_chain_map_card_eq_local M L]
            exact subgroup_card_lt_of_lt_top_local M L hL
          have hEq : Nat.card LX = Nat.card MX.1 := by simpa [hLXtop]
          exact (lt_irrefl _ (hEq ▸ hlt)).elim
        have hstep := hrec.1 LX hLXproper (mapped_linear_character_local M L χ)
        dsimp [LX, MX] at hstep
        rcases hstep with ⟨c, hc⟩
        refine ⟨c, ?_⟩
        -- Reinterpret the recursive ambient witness on `M.map H.subtype` as the smaller-ambient
        -- pairing statement needed for the coatom transport step.
        calc
          linear_character_pairing_int M L χ
              (Subgroup.characterRingTransport
                ((L.map M.subtype).equivMapOfInjective H.1.subtype
                  H.1.subtype_injective)
                (x
                  ⟨(L.map M.subtype).map H.1.subtype,
                    (hXelem ((L.map M.subtype).map H.1.subtype)).2 <|
                      isElementary_of_mulEquiv_local
                        ((L.map M.subtype).equivMapOfInjective H.1.subtype
                          H.1.subtype_injective)
                        (subgroup_isElementary_of_isElementary_local (L.map M.subtype)
                          (isElementary_of_mulEquiv_local
                            (M.equivMapOfInjective H.1.subtype H.1.subtype_injective)
                            (subgroup_isElementary_of_isElementary_local M
                              ((hXelem H.1).1 H.2))))⟩)) =
              linear_character_pairing_int H.1 (L.map M.subtype)
                (mapped_linear_character_local M L χ)
                (x
                  ⟨(L.map M.subtype).map H.1.subtype,
                    (hXelem ((L.map M.subtype).map H.1.subtype)).2 <|
                      isElementary_of_mulEquiv_local
                        ((L.map M.subtype).equivMapOfInjective H.1.subtype
                          H.1.subtype_injective)
                        (subgroup_isElementary_of_isElementary_local (L.map M.subtype)
                          (isElementary_of_mulEquiv_local
                            (M.equivMapOfInjective H.1.subtype H.1.subtype_injective)
                            (subgroup_isElementary_of_isElementary_local M
                              ((hXelem H.1).1 H.2))))⟩) := by
                  symm
                  exact
                    linear_character_pairing_int_subgroupOf_eq H.1 M L χ
                      (x
                        ⟨(L.map M.subtype).map H.1.subtype,
                          (hXelem ((L.map M.subtype).map H.1.subtype)).2 <|
                            isElementary_of_mulEquiv_local
                              ((L.map M.subtype).equivMapOfInjective H.1.subtype
                                H.1.subtype_injective)
                              (subgroup_isElementary_of_isElementary_local
                                (L.map M.subtype)
                                (isElementary_of_mulEquiv_local
                                  (M.equivMapOfInjective H.1.subtype
                                    H.1.subtype_injective)
                                  (subgroup_isElementary_of_isElementary_local M
                                    ((hXelem H.1).1 H.2))))⟩)
          _ = n * c := hc
      have htopM :
          ∀ χ : M →* ℂˣ,
            let MX : X := ⟨M.map H.1.subtype,
              (hXelem (M.map H.1.subtype)).2 <|
                isElementary_of_mulEquiv_local
                  (M.equivMapOfInjective H.1.subtype H.1.subtype_injective)
                  (subgroup_isElementary_of_isElementary_local M
                    ((hXelem H.1).1 H.2))⟩
            ∃ b : ℤ,
              ⟪(χ.toCharacterRing : M → ℂ),
                  ((Subgroup.characterRingTransport
                    (M.equivMapOfInjective H.1.subtype H.1.subtype_injective)
                    (x MX) : R(M)) : M → ℂ)⟫ =
                algebraMap ℤ ℂ (n * b) := by
        intro χ
        let βM : MX.1 →* ℂˣ := mapped_linear_character_local H.1 M χ
        let αM : (⊤ : Subgroup MX.1) →* ℂˣ := βM.comp Subgroup.topEquiv.symm.toMonoidHom
        have htop_local := hrec.2 αM
        have htop_transport :
            ∃ c : ℤ, linear_character_pairing_int MX.1 (⊤ : Subgroup MX.1) αM (x MX) = n * c := by
          -- Convert the recursive top witness on the chosen smaller-ambient splitting back to the
          -- actual `x MX` coordinate through the residual theorem.
          exact
            residual_subgroup_pairing_int_divisible_of_given_top_local_pairing
              X hXelem s hs hn hx hdx MX sM hsM (⊤ : Subgroup MX.1) αM htop_local
        rcases htop_transport with ⟨c, hc⟩
        refine ⟨c, ?_⟩
        have hβpair :
            ⟪(βM.toCharacterRing : MX.1 → ℂ), (x MX : MX.1 → ℂ)⟫ =
              algebraMap ℤ ℂ (n * c) := by
          have htop_pair :
              ⟪(αM.toCharacterRing : (⊤ : Subgroup MX.1) → ℂ),
                  ((Subgroup.characterRingTransport
                    (Subgroup.topEquiv : (⊤ : Subgroup MX.1) ≃* MX.1)
                    (x MX) : R((⊤ : Subgroup MX.1))) :
                      (⊤ : Subgroup MX.1) → ℂ)⟫ =
                algebraMap ℤ ℂ (n * c) := by
            simpa using
              congrArg (algebraMap ℤ ℂ) hc |>.trans
                (subgroup_linear_character_pairing_int_transport_eq
                  (H := MX.1) (K := (⊤ : Subgroup MX.1)) (χ := αM) (η := x MX)).symm
          calc
            ⟪(βM.toCharacterRing : MX.1 → ℂ), (x MX : MX.1 → ℂ)⟫ =
                ⟪(αM.toCharacterRing : (⊤ : Subgroup MX.1) → ℂ),
                    ((Subgroup.characterRingTransport
                      (Subgroup.topEquiv : (⊤ : Subgroup MX.1) ≃* MX.1)
                      (x MX) : R((⊤ : Subgroup MX.1))) :
                        (⊤ : Subgroup MX.1) → ℂ)⟫ := by
                  simpa [βM, αM] using
                    (linear_character_pairing_transport_eq
                      (H := MX.1) (K := (⊤ : Subgroup MX.1)) (χ := αM) (η := x MX)).symm
            _ = algebraMap ℤ ℂ (n * c) := htop_pair
        -- Transport the ambient character on `M.map H.subtype` back to `M`.
        calc
          ⟪(χ.toCharacterRing : M → ℂ),
              ((Subgroup.characterRingTransport
                (M.equivMapOfInjective H.1.subtype H.1.subtype_injective)
                (x MX) : R(M)) : M → ℂ)⟫ =
            ⟪(βM.toCharacterRing : MX.1 → ℂ), (x MX : MX.1 → ℂ)⟫ := by
              exact
                (linear_character_pairing_transport_eq
                  (H := H.1) (K := M) (χ := χ) (η := x MX)).symm
          _ = algebraMap ℤ ℂ (n * c) := hβpair
      -- The coatom bridge consumes the recursive proper and top witnesses in the smaller ambient.
      exact
        coatom_cover_step_for_hproper_all
          X hXelem s hs hn hx hdx H sH hsH M J hJ hJM α hproperM htopM
    refine And.intro ?_ ?_
    · -- The proper-subgroup component is the first output of the strong owner.
      exact hproper_all
    · intro α
      let XH : Finset (Subgroup H.1) := Finset.univ
      let ψH : (J : XH) → R(J.1) := fun J ↦
        Subgroup.characterRingTransport
          (J.1.equivMapOfInjective H.1.subtype H.1.subtype_injective)
          (x ⟨J.1.map H.1.subtype,
            (hXelem (J.1.map H.1.subtype)).2 <|
              isElementary_of_mulEquiv_local
                (J.1.equivMapOfInjective H.1.subtype H.1.subtype_injective)
                (subgroup_isElementary_of_isElementary_local J.1 ((hXelem H.1).1 H.2))⟩)
      have hpackage :
          let XH : Finset (Subgroup H.1) := Finset.univ
          let ψH : (J : XH) → R(J.1) := fun J ↦
            Subgroup.characterRingTransport
              (J.1.equivMapOfInjective H.1.subtype H.1.subtype_injective)
              (x ⟨J.1.map H.1.subtype,
                (hXelem (J.1.map H.1.subtype)).2 <|
                  isElementary_of_mulEquiv_local
                    (J.1.equivMapOfInjective H.1.subtype H.1.subtype_injective)
                    (subgroup_isElementary_of_isElementary_local J.1 ((hXelem H.1).1 H.2))⟩)
          let ξH : R(H.1) := sH ψH
          (∃ b₀ : ℤ, ⟪((1 : R(H.1)) : H.1 → ℂ), (ξH : H.1 → ℂ)⟫ =
              algebraMap ℤ ℂ (n * b₀)) ∧
            ∀ α : (⊤ : Subgroup H.1) →* ℂˣ,
              ∃ b : ℤ,
                ⟪((Subgroup.characterRingInduction (⊤ : Subgroup H.1)
                      (α.toCharacterRing - 1) : R(H.1)) : H.1 → ℂ),
                    (ξH : H.1 → ℂ)⟫ =
                  algebraMap ℤ ℂ (n * b) := by
        simpa using
          coatom_quotient_pairing_divisible_package_core_of_proper_branch
            X hXelem s hs hn hx hdx H sH hsH hproper_all
      -- Recombine the trivial-line and top-difference package into the actual top local pairing.
      simpa [XH, ψH] using
        top_local_pairing_divisible_of_trivial_and_top_difference_pairings
          (n := n) sH ψH α hpackage.1 (hpackage.2 α)
  have hall : ∀ m, P m := by
    intro m
    apply Nat.strong_induction_on m
    intro k hk
    exact hP k hk
  exact hall (Nat.card H.1) H rfl sH hsH

/-- Helper for Remark 11-11.1-3: this is the proper-subgroup branch of the source proof. For a
proper subgroup `J < H`, the induced linear-character pairing against the top local image is an
`n`-multiple. -/
private theorem ambient_local_pairing_divisibility_package_of_defect_multiple
    (X : Finset (Subgroup G))
    (hXelem : ∀ H : Subgroup G, H ∈ X ↔ IsElementary H)
    (s : ((H : X) → R(H.1)) →ₗ[ℤ] R(G))
    (hs : Function.LeftInverse s (Representation.characterRingRestriction X).toLinearMap)
    {x : (H : X) → R(H.1)} {t : elementary_coherence_target X hXelem} {n : ℤ}
    (hn : n ≠ 0) (hx : s x = 0)
    (hdx : elementary_coherence_defect X hXelem x = n • t)
    (H : X)
    (sH : ((J : (Finset.univ : Finset (Subgroup H.1))) → R(J.1)) →ₗ[ℤ] R(H.1))
    (hsH : Function.LeftInverse sH
      (Representation.characterRingRestriction (Finset.univ : Finset (Subgroup H.1))).toLinearMap) :
    (∀ (J : Subgroup H.1) (hJ : J < ⊤) (α : J →* ℂˣ),
      let KX : X := ⟨J.map H.1.subtype,
        (hXelem (J.map H.1.subtype)).2 <|
          isElementary_of_mulEquiv_local
            (J.equivMapOfInjective H.1.subtype H.1.subtype_injective)
            (subgroup_isElementary_of_isElementary_local J ((hXelem H.1).1 H.2))⟩
      ∃ c : ℤ, linear_character_pairing_int H.1 J α (x KX) = n * c) ∧
      (∀ α : (⊤ : Subgroup H.1) →* ℂˣ,
        let XH : Finset (Subgroup H.1) := Finset.univ
        let ψH : (J : XH) → R(J.1) := fun J ↦
          Subgroup.characterRingTransport
            (J.1.equivMapOfInjective H.1.subtype H.1.subtype_injective)
            (x ⟨J.1.map H.1.subtype,
              (hXelem (J.1.map H.1.subtype)).2 <|
                isElementary_of_mulEquiv_local
                  (J.1.equivMapOfInjective H.1.subtype H.1.subtype_injective)
                  (subgroup_isElementary_of_isElementary_local J.1 ((hXelem H.1).1 H.2))⟩)
      let K0 : XH := ⟨⊤, by simp [XH]⟩
      ∃ b : ℤ,
          ⟪(α.toCharacterRing : (⊤ : Subgroup H.1) → ℂ),
            (((Representation.characterRingRestriction XH) (sH ψH) K0 : R((⊤ : Subgroup H.1))) :
                (⊤ : Subgroup H.1) → ℂ)⟫ =
            algebraMap ℤ ℂ (n * b)) := by
  classical
  -- The old theorem name is now just the interface wrapper used by later declarations.
  simpa using
    ambient_local_pairing_divisibility_package_strong_induction
      X hXelem s hs hn hx hdx H sH hsH

/-- Helper for Remark 11-11.1-3: project the top-local witness from the joint ambient package so
the coatom branch can consume it on a smaller ambient subgroup without rebuilding the induction.
-/
private theorem top_local_pairing_divisible_of_defect_multiple_on_smaller_ambient
    (X : Finset (Subgroup G))
    (hXelem : ∀ H : Subgroup G, H ∈ X ↔ IsElementary H)
    (s : ((H : X) → R(H.1)) →ₗ[ℤ] R(G))
    (hs : Function.LeftInverse s (Representation.characterRingRestriction X).toLinearMap)
    {x : (H : X) → R(H.1)} {t : elementary_coherence_target X hXelem} {n : ℤ}
    (hn : n ≠ 0) (hx : s x = 0)
    (hdx : elementary_coherence_defect X hXelem x = n • t)
    (H : X)
    (sH : ((J : (Finset.univ : Finset (Subgroup H.1))) → R(J.1)) →ₗ[ℤ] R(H.1))
    (hsH : Function.LeftInverse sH
      (Representation.characterRingRestriction (Finset.univ : Finset (Subgroup H.1))).toLinearMap)
    (α : (⊤ : Subgroup H.1) →* ℂˣ) :
    let XH : Finset (Subgroup H.1) := Finset.univ
    let ψH : (J : XH) → R(J.1) := fun J ↦
      Subgroup.characterRingTransport
        (J.1.equivMapOfInjective H.1.subtype H.1.subtype_injective)
        (x ⟨J.1.map H.1.subtype,
          (hXelem (J.1.map H.1.subtype)).2 <|
            isElementary_of_mulEquiv_local
              (J.1.equivMapOfInjective H.1.subtype H.1.subtype_injective)
              (subgroup_isElementary_of_isElementary_local J.1 ((hXelem H.1).1 H.2))⟩)
    let K0 : XH := ⟨⊤, by simp [XH]⟩
    ∃ b : ℤ,
      ⟪(α.toCharacterRing : (⊤ : Subgroup H.1) → ℂ),
          (((Representation.characterRingRestriction XH) (sH ψH) K0 : R((⊤ : Subgroup H.1))) :
            (⊤ : Subgroup H.1) → ℂ)⟫ =
        algebraMap ℤ ℂ (n * b) := by
  classical
  -- The joint package is the owner theorem; this is only the interface projection used later in
  -- the coatom branch.
  simpa using
    (ambient_local_pairing_divisibility_package_of_defect_multiple
      X hXelem s hs hn hx hdx H sH hsH).2 α

/-- Helper for Remark 11-11.1-3: this is the proper-subgroup branch of the source proof. For a
proper subgroup `J < H`, the induced linear-character pairing against the top local image is an
`n`-multiple. -/
private theorem proper_subgroup_pairing_int_divisible_of_defect_multiple
    (X : Finset (Subgroup G))
    (hXelem : ∀ H : Subgroup G, H ∈ X ↔ IsElementary H)
    (s : ((H : X) → R(H.1)) →ₗ[ℤ] R(G))
    (hs : Function.LeftInverse s (Representation.characterRingRestriction X).toLinearMap)
    {x : (H : X) → R(H.1)} {t : elementary_coherence_target X hXelem} {n : ℤ}
    (hn : n ≠ 0) (hx : s x = 0)
    (hdx : elementary_coherence_defect X hXelem x = n • t)
    (H : X) (J : Subgroup H.1) (hJ : J < ⊤) (α : J →* ℂˣ) :
    let KX : X := ⟨J.map H.1.subtype,
      (hXelem (J.map H.1.subtype)).2 <|
        isElementary_of_mulEquiv_local
          (J.equivMapOfInjective H.1.subtype H.1.subtype_injective)
          (subgroup_isElementary_of_isElementary_local J ((hXelem H.1).1 H.2))⟩
    ∃ c : ℤ, linear_character_pairing_int H.1 J α (x KX) = n * c := by
  classical
  obtain ⟨sH, hsH⟩ :=
    characterRingRestriction_has_leftInverse_of_detection_by_restrictions
      (G := H.1) (Finset.univ : Finset (Subgroup H.1))
      subgroup_restriction_detection_on_elementary_group
  -- Project the proper-subgroup component from the joint ambient package so the coatom recursion
  -- is owned in one place instead of being rebuilt here.
  simpa using
    (ambient_local_pairing_divisibility_package_of_defect_multiple
      X hXelem s hs hn hx hdx H sH hsH).1 J hJ α

/-- Helper for Remark 11-11.1-3: this is the proper-subgroup branch of the source proof. For a
proper subgroup `J < H`, the induced linear-character pairing against the top local image is an
`n`-multiple. -/
private theorem proper_induced_pairing_divisible_of_residual_family
    (X : Finset (Subgroup G))
    (hXelem : ∀ H : Subgroup G, H ∈ X ↔ IsElementary H)
    (s : ((H : X) → R(H.1)) →ₗ[ℤ] R(G))
    (hs : Function.LeftInverse s (Representation.characterRingRestriction X).toLinearMap)
    {x : (H : X) → R(H.1)} {t : elementary_coherence_target X hXelem} {n : ℤ}
    (hn : n ≠ 0) (hx : s x = 0)
    (hdx : elementary_coherence_defect X hXelem x = n • t)
    (H : X)
    (sH : ((J : (Finset.univ : Finset (Subgroup H.1))) → R(J.1)) →ₗ[ℤ] R(H.1))
    (hsH : Function.LeftInverse sH
      (Representation.characterRingRestriction (Finset.univ : Finset (Subgroup H.1))).toLinearMap)
    (J : Subgroup H.1) (hJ : J < ⊤) (α : J →* ℂˣ) :
    let XH : Finset (Subgroup H.1) := Finset.univ
    let ψH : (K : XH) → R(K.1) := fun K ↦
      Subgroup.characterRingTransport
        (K.1.equivMapOfInjective H.1.subtype H.1.subtype_injective)
        (x ⟨K.1.map H.1.subtype,
          (hXelem (K.1.map H.1.subtype)).2 <|
            isElementary_of_mulEquiv_local
              (K.1.equivMapOfInjective H.1.subtype H.1.subtype_injective)
              (subgroup_isElementary_of_isElementary_local K.1 ((hXelem H.1).1 H.2))⟩)
    let ξH : R(H.1) := sH ψH
    ∃ b : ℤ,
        ⟪Ind[J](α.toRepresentation.character), (ξH : H.1 → ℂ)⟫ =
          algebraMap ℤ ℂ (n * b) := by
  classical
  -- Route correction: isolate the proper-subgroup branch as its own owner lemma before the
  -- coatom argument, exactly as in the source proof.
  dsimp
  obtain ⟨c, hc⟩ :=
    proper_subgroup_pairing_int_divisible_of_defect_multiple
      X hXelem s hs hn hx hdx H J hJ α
  -- Feed the isolated arithmetic premise into the already-proved transport-to-induced wrapper.
  exact
    proper_induced_pairing_divisible_of_transport_pairing_int_divisible
      X hXelem hdx H sH hsH J α ⟨c, hc⟩

/-- Helper for Remark 11-11.1-3: the coatom quotient step depends only on the already established
proper-subgroup arithmetic branch, so the later residual-family theorem can be a corollary rather
than a second owner of the quotient argument. -/
private theorem coatom_quotient_pairing_divisible_package_of_proper_branch
    (X : Finset (Subgroup G))
    (hXelem : ∀ H : Subgroup G, H ∈ X ↔ IsElementary H)
    (s : ((H : X) → R(H.1)) →ₗ[ℤ] R(G))
    (hs : Function.LeftInverse s (Representation.characterRingRestriction X).toLinearMap)
    {x : (H : X) → R(H.1)} {t : elementary_coherence_target X hXelem} {n : ℤ}
    (hn : n ≠ 0) (hx : s x = 0)
    (hdx : elementary_coherence_defect X hXelem x = n • t)
    (H : X)
    (sH : ((J : (Finset.univ : Finset (Subgroup H.1))) → R(J.1)) →ₗ[ℤ] R(H.1))
    (hsH : Function.LeftInverse sH
      (Representation.characterRingRestriction (Finset.univ : Finset (Subgroup H.1))).toLinearMap)
    (hproper :
      ∀ (J : Subgroup H.1) (hJ : J < ⊤) (α : J →* ℂˣ),
        let KX : X := ⟨J.map H.1.subtype,
          (hXelem (J.map H.1.subtype)).2 <|
            isElementary_of_mulEquiv_local
              (J.equivMapOfInjective H.1.subtype H.1.subtype_injective)
              (subgroup_isElementary_of_isElementary_local J ((hXelem H.1).1 H.2))⟩
        ∃ c : ℤ, linear_character_pairing_int H.1 J α (x KX) = n * c) :
    let XH : Finset (Subgroup H.1) := Finset.univ
    let ψH : (J : XH) → R(J.1) := fun J ↦
      Subgroup.characterRingTransport
        (J.1.equivMapOfInjective H.1.subtype H.1.subtype_injective)
        (x ⟨J.1.map H.1.subtype,
          (hXelem (J.1.map H.1.subtype)).2 <|
            isElementary_of_mulEquiv_local
              (J.1.equivMapOfInjective H.1.subtype H.1.subtype_injective)
              (subgroup_isElementary_of_isElementary_local J.1 ((hXelem H.1).1 H.2))⟩)
    let ξH : R(H.1) := sH ψH
    (∃ b₀ : ℤ, ⟪((1 : R(H.1)) : H.1 → ℂ), (ξH : H.1 → ℂ)⟫ = algebraMap ℤ ℂ (n * b₀)) ∧
      ∀ α : (⊤ : Subgroup H.1) →* ℂˣ,
        ∃ b : ℤ,
          ⟪((Subgroup.characterRingInduction (⊤ : Subgroup H.1)
                (α.toCharacterRing - 1) : R(H.1)) : H.1 → ℂ),
              (ξH : H.1 → ℂ)⟫ =
            algebraMap ℤ ℂ (n * b) := by
  classical
  -- Route correction: the quotient argument belongs in one helper that consumes only the proper
  -- arithmetic branch. The ambient induction theorem and the residual-family theorem should both
  -- reuse this package instead of duplicating the prime-quotient analysis.
  simpa using
    coatom_quotient_pairing_divisible_package_core_of_proper_branch
      X hXelem s hs hn hx hdx H sH hsH hproper

/-- Helper for Remark 11-11.1-3: this packages the Chapter 10 coatom step for the top-subgroup
branch. It simultaneously controls the trivial line and the top generators
`Ind_⊤^H(α - 1)`. -/
private theorem coatom_quotient_pairing_divisible_package_of_residual_family
    (X : Finset (Subgroup G))
    (hXelem : ∀ H : Subgroup G, H ∈ X ↔ IsElementary H)
    (s : ((H : X) → R(H.1)) →ₗ[ℤ] R(G))
    (hs : Function.LeftInverse s (Representation.characterRingRestriction X).toLinearMap)
    {x : (H : X) → R(H.1)} {t : elementary_coherence_target X hXelem} {n : ℤ}
    (hn : n ≠ 0) (hx : s x = 0)
    (hdx : elementary_coherence_defect X hXelem x = n • t)
    (H : X)
    (sH : ((J : (Finset.univ : Finset (Subgroup H.1))) → R(J.1)) →ₗ[ℤ] R(H.1))
    (hsH : Function.LeftInverse sH
      (Representation.characterRingRestriction (Finset.univ : Finset (Subgroup H.1))).toLinearMap) :
    let XH : Finset (Subgroup H.1) := Finset.univ
    let ψH : (J : XH) → R(J.1) := fun J ↦
      Subgroup.characterRingTransport
        (J.1.equivMapOfInjective H.1.subtype H.1.subtype_injective)
        (x ⟨J.1.map H.1.subtype,
          (hXelem (J.1.map H.1.subtype)).2 <|
            isElementary_of_mulEquiv_local
              (J.1.equivMapOfInjective H.1.subtype H.1.subtype_injective)
              (subgroup_isElementary_of_isElementary_local J.1 ((hXelem H.1).1 H.2))⟩)
    let ξH : R(H.1) := sH ψH
    (∃ b₀ : ℤ, ⟪((1 : R(H.1)) : H.1 → ℂ), (ξH : H.1 → ℂ)⟫ = algebraMap ℤ ℂ (n * b₀)) ∧
      ∀ α : (⊤ : Subgroup H.1) →* ℂˣ,
        ∃ b : ℤ,
          ⟪((Subgroup.characterRingInduction (⊤ : Subgroup H.1)
                (α.toCharacterRing - 1) : R(H.1)) : H.1 → ℂ),
              (ξH : H.1 → ℂ)⟫ =
            algebraMap ℤ ℂ (n * b) := by
  classical
  -- The residual-family theorem now only repackages the proper branch through the dedicated
  -- coatom helper; it no longer owns a second copy of the quotient argument.
  dsimp
  exact
    coatom_quotient_pairing_divisible_package_of_proper_branch
      X hXelem s hs hn hx hdx H sH hsH
      (fun J hJ α ↦
        (ambient_local_pairing_divisibility_package_of_defect_multiple
          X hXelem s hs hn hx hdx H sH hsH).1 J hJ α)

/-- Helper for Remark 11-11.1-3: isolate the trivial-character line before reassembling the full
elementary span `R'`. -/
private theorem top_local_image_trivial_pairing_divisible_of_residual_family
    (X : Finset (Subgroup G))
    (hXelem : ∀ H : Subgroup G, H ∈ X ↔ IsElementary H)
    (s : ((H : X) → R(H.1)) →ₗ[ℤ] R(G))
    (hs : Function.LeftInverse s (Representation.characterRingRestriction X).toLinearMap)
    {x : (H : X) → R(H.1)} {t : elementary_coherence_target X hXelem} {n : ℤ}
    (hn : n ≠ 0) (hx : s x = 0)
    (hdx : elementary_coherence_defect X hXelem x = n • t)
    (H : X)
    (sH : ((J : (Finset.univ : Finset (Subgroup H.1))) → R(J.1)) →ₗ[ℤ] R(H.1))
    (hsH : Function.LeftInverse sH
      (Representation.characterRingRestriction (Finset.univ : Finset (Subgroup H.1))).toLinearMap) :
    let XH : Finset (Subgroup H.1) := Finset.univ
    let ψH : (J : XH) → R(J.1) := fun J ↦
      Subgroup.characterRingTransport
        (J.1.equivMapOfInjective H.1.subtype H.1.subtype_injective)
        (x ⟨J.1.map H.1.subtype,
          (hXelem (J.1.map H.1.subtype)).2 <|
            isElementary_of_mulEquiv_local
              (J.1.equivMapOfInjective H.1.subtype H.1.subtype_injective)
              (subgroup_isElementary_of_isElementary_local J.1 ((hXelem H.1).1 H.2))⟩)
    let ξH : R(H.1) := sH ψH
    ∃ b : ℤ, ⟪((1 : R(H.1)) : H.1 → ℂ), (ξH : H.1 → ℂ)⟫ = algebraMap ℤ ℂ (n * b) := by
  classical
  -- Route correction: the old proof tried to consume the augmentation relation for
  -- `Ind[K](χ) - [H : K] · 1` directly. The source proof first isolates the trivial-character
  -- line via the Chapter 10 coatom quotient package before reassembling the whole span `R'`.
  dsimp
  exact
    (coatom_quotient_pairing_divisible_package_of_residual_family
      X hXelem s hs hn hx hdx H sH hsH).1

/-- Helper for Remark 11-11.1-3: once the trivial-character line is controlled, every element of
that line pairs with the top local image by an `n`-multiple. -/
private theorem pairing_divisible_of_mem_trivial_character_line_of_residual_family
    (X : Finset (Subgroup G))
    (hXelem : ∀ H : Subgroup G, H ∈ X ↔ IsElementary H)
    (s : ((H : X) → R(H.1)) →ₗ[ℤ] R(G))
    (hs : Function.LeftInverse s (Representation.characterRingRestriction X).toLinearMap)
    {x : (H : X) → R(H.1)} {t : elementary_coherence_target X hXelem} {n : ℤ}
    (hn : n ≠ 0) (hx : s x = 0)
    (hdx : elementary_coherence_defect X hXelem x = n • t)
    (H : X)
    (sH : ((J : (Finset.univ : Finset (Subgroup H.1))) → R(J.1)) →ₗ[ℤ] R(H.1))
    (hsH : Function.LeftInverse sH
      (Representation.characterRingRestriction (Finset.univ : Finset (Subgroup H.1))).toLinearMap)
    (η : R(H.1))
    (hη : η ∈ Submodule.span ℤ ({1} : Set (R(H.1)))) :
    let XH : Finset (Subgroup H.1) := Finset.univ
    let ψH : (J : XH) → R(J.1) := fun J ↦
      Subgroup.characterRingTransport
        (J.1.equivMapOfInjective H.1.subtype H.1.subtype_injective)
        (x ⟨J.1.map H.1.subtype,
          (hXelem (J.1.map H.1.subtype)).2 <|
            isElementary_of_mulEquiv_local
              (J.1.equivMapOfInjective H.1.subtype H.1.subtype_injective)
              (subgroup_isElementary_of_isElementary_local J.1 ((hXelem H.1).1 H.2))⟩)
    let ξH : R(H.1) := sH ψH
    ∃ b : ℤ, ⟪(η : H.1 → ℂ), (ξH : H.1 → ℂ)⟫ = algebraMap ℤ ℂ (n * b) := by
  classical
  dsimp
  let ξH : R(H.1) := sH ψH
  rcases Submodule.mem_span_singleton.mp hη with ⟨m, rfl⟩
  obtain ⟨b, hb⟩ :=
    top_local_image_trivial_pairing_divisible_of_residual_family
      X hXelem s hs hn hx hdx H sH hsH
  refine ⟨m * b, ?_⟩
  -- Reduce the whole line to the previously isolated trivial-character case.
  calc
    ⟪(((m • (1 : R(H.1))) : R(H.1)) : H.1 → ℂ), (ξH : H.1 → ℂ)⟫ =
        (m : ℂ) * ⟪((1 : R(H.1)) : H.1 → ℂ), (ξH : H.1 → ℂ)⟫ := by
          simpa using
            (Representation.groupFunctionPairing_smul_left
              (a := (m : ℂ)) (φ := ((1 : R(H.1)) : H.1 → ℂ)) (ψ := (ξH : H.1 → ℂ)))
    _ = (m : ℂ) * algebraMap ℤ ℂ (n * b) := by rw [hb]
    _ = algebraMap ℤ ℂ (n * (m * b)) := by
          simp [Int.cast_mul, mul_assoc, mul_left_comm, mul_comm]

/-- Helper for Remark 11-11.1-3: the augmentation summand `R₀'` is the inner source-faithful
owner statement for the top local image divisibility argument. -/
private theorem pairing_divisible_of_mem_elementaryLinearCharacterAugmentationSpan_of_residual_family
    (X : Finset (Subgroup G))
    (hXelem : ∀ H : Subgroup G, H ∈ X ↔ IsElementary H)
    (s : ((H : X) → R(H.1)) →ₗ[ℤ] R(G))
    (hs : Function.LeftInverse s (Representation.characterRingRestriction X).toLinearMap)
    {x : (H : X) → R(H.1)} {t : elementary_coherence_target X hXelem} {n : ℤ}
    (hn : n ≠ 0) (hx : s x = 0)
    (hdx : elementary_coherence_defect X hXelem x = n • t)
    (H : X)
    (sH : ((J : (Finset.univ : Finset (Subgroup H.1))) → R(J.1)) →ₗ[ℤ] R(H.1))
    (hsH : Function.LeftInverse sH
      (Representation.characterRingRestriction (Finset.univ : Finset (Subgroup H.1))).toLinearMap)
    (η : R(H.1)) (hη : η ∈ R₀'(H.1)) :
    let XH : Finset (Subgroup H.1) := Finset.univ
    let ψH : (J : XH) → R(J.1) := fun J ↦
      Subgroup.characterRingTransport
        (J.1.equivMapOfInjective H.1.subtype H.1.subtype_injective)
        (x ⟨J.1.map H.1.subtype,
          (hXelem (J.1.map H.1.subtype)).2 <|
            isElementary_of_mulEquiv_local
              (J.1.equivMapOfInjective H.1.subtype H.1.subtype_injective)
              (subgroup_isElementary_of_isElementary_local J.1 ((hXelem H.1).1 H.2))⟩)
    let ξH : R(H.1) := sH ψH
    ∃ b : ℤ, ⟪(η : H.1 → ℂ), (ξH : H.1 → ℂ)⟫ = algebraMap ℤ ℂ (n * b) := by
  classical
  -- Route correction: this is the actual owner statement for the source proof. The outer theorem
  -- on `R'` should only reassemble `ℤ · 1` with `R₀'`, not rediscover the generator analysis.
  dsimp
  rw [elementaryLinearCharacterAugmentationSpan] at hη
  induction hη using Submodule.span_induction with
  | mem ζ hζ =>
      rcases hζ with ⟨E, hEelem, α, rfl⟩
      by_cases hEtop : E = ⊤
      · subst hEtop
        -- The source top-subgroup generator branch is exactly the second output of the coatom
        -- package.
        exact
          (coatom_quotient_pairing_divisible_package_of_residual_family
            X hXelem s hs hn hx hdx H sH hsH).2 α
      · have hEproper : E < ⊤ := lt_of_le_of_ne le_top hEtop
        -- The source proper-subgroup generator branch is handled once by the dedicated proper
        -- induced-pairing lemma.
        exact
          proper_induced_pairing_divisible_of_residual_family
            X hXelem s hs hn hx hdx H sH hsH E hEproper α
  | zero =>
      refine ⟨0, ?_⟩
      simp [Representation.groupFunctionPairingOverField]
  | add η₁ η₂ _ _ hη₁ hη₂ =>
      rcases hη₁ with ⟨b₁, hb₁⟩
      rcases hη₂ with ⟨b₂, hb₂⟩
      refine ⟨b₁ + b₂, ?_⟩
      -- Pairing is additive in the left variable, so the two divisibility witnesses add.
      calc
        ⟪((η₁ + η₂ : R(H.1)) : H.1 → ℂ), ((sH ψH : R(H.1)) : H.1 → ℂ)⟫ =
            ⟪(η₁ : H.1 → ℂ), ((sH ψH : R(H.1)) : H.1 → ℂ)⟫ +
              ⟪(η₂ : H.1 → ℂ), ((sH ψH : R(H.1)) : H.1 → ℂ)⟫ := by
                exact
                  Representation.groupFunctionPairing_add_left
                    (η₁ : H.1 → ℂ) (η₂ : H.1 → ℂ)
                    (((sH ψH : R(H.1)) : H.1 → ℂ))
        _ = algebraMap ℤ ℂ (n * b₁) + algebraMap ℤ ℂ (n * b₂) := by rw [hb₁, hb₂]
        _ = algebraMap ℤ ℂ (n * (b₁ + b₂)) := by
              rw [← Int.cast_add]
              congr 1
              ring
  | smul m η _ hη =>
      rcases hη with ⟨b, hb⟩
      refine ⟨m * b, ?_⟩
      -- Pairing is `ℤ`-linear in the left variable, so scalar multiples preserve divisibility.
      calc
        ⟪(((m • η : R(H.1)) : H.1 → ℂ)), ((sH ψH : R(H.1)) : H.1 → ℂ)⟫ =
            (m : ℂ) * ⟪(η : H.1 → ℂ), ((sH ψH : R(H.1)) : H.1 → ℂ)⟫ := by
              simpa [zsmul_eq_mul] using
                (Representation.groupFunctionPairing_smul_left
                  (a := (m : ℂ)) (φ := (η : H.1 → ℂ))
                  (ψ := (((sH ψH : R(H.1)) : H.1 → ℂ))))
        _ = (m : ℂ) * algebraMap ℤ ℂ (n * b) := by rw [hb]
        _ = algebraMap ℤ ℂ (n * (m * b)) := by
              simp [Int.cast_mul, mul_assoc, mul_left_comm, mul_comm]

/-- Helper for Remark 11-11.1-3: the remaining source-faithful endgame is that the explicit local
image term coming from the chosen splitting has all of its linear pairings divisible by `n`. -/
private theorem pairing_divisible_of_mem_elementaryLinearCharacterSpan_of_residual_family
    (X : Finset (Subgroup G))
    (hXelem : ∀ H : Subgroup G, H ∈ X ↔ IsElementary H)
    (s : ((H : X) → R(H.1)) →ₗ[ℤ] R(G))
    (hs : Function.LeftInverse s (Representation.characterRingRestriction X).toLinearMap)
    {x : (H : X) → R(H.1)} {t : elementary_coherence_target X hXelem} {n : ℤ}
    (hn : n ≠ 0) (hx : s x = 0)
    (hdx : elementary_coherence_defect X hXelem x = n • t)
    (H : X)
    (sH : ((J : (Finset.univ : Finset (Subgroup H.1))) → R(J.1)) →ₗ[ℤ] R(H.1))
    (hsH : Function.LeftInverse sH
      (Representation.characterRingRestriction (Finset.univ : Finset (Subgroup H.1))).toLinearMap)
    (η : R(H.1)) (hη : η ∈ R'(H.1)) :
    let XH : Finset (Subgroup H.1) := Finset.univ
    let ψH : (J : XH) → R(J.1) := fun J ↦
      Subgroup.characterRingTransport
        (J.1.equivMapOfInjective H.1.subtype H.1.subtype_injective)
        (x ⟨J.1.map H.1.subtype,
          (hXelem (J.1.map H.1.subtype)).2 <|
            isElementary_of_mulEquiv_local
              (J.1.equivMapOfInjective H.1.subtype H.1.subtype_injective)
              (subgroup_isElementary_of_isElementary_local J.1 ((hXelem H.1).1 H.2))⟩)
    let ξH : R(H.1) := sH ψH
    ∃ b : ℤ, ⟪(η : H.1 → ℂ), (ξH : H.1 → ℂ)⟫ = algebraMap ℤ ℂ (n * b) := by
  classical
  dsimp
  let ξH : R(H.1) := sH ψH
  rw [elementaryLinearCharacterSpan] at hη
  rcases Submodule.mem_sup.mp hη with ⟨η₁, hη₁, η₀, hη₀, rfl⟩
  obtain ⟨b₁, hb₁⟩ :=
    pairing_divisible_of_mem_trivial_character_line_of_residual_family
      X hXelem s hs hn hx hdx H sH hsH η₁ hη₁
  obtain ⟨b₀, hb₀⟩ :=
    pairing_divisible_of_mem_elementaryLinearCharacterAugmentationSpan_of_residual_family
      X hXelem s hs hn hx hdx H sH hsH η₀ hη₀
  refine ⟨b₁ + b₀, ?_⟩
  -- Reassemble the outer decomposition `R' = ℤ · 1 ⊔ R₀'` additively at the pairing level.
  calc
    ⟪((η₁ + η₀ : R(H.1)) : H.1 → ℂ), (ξH : H.1 → ℂ)⟫ =
        ⟪(η₁ : H.1 → ℂ), (ξH : H.1 → ℂ)⟫ +
          ⟪(η₀ : H.1 → ℂ), (ξH : H.1 → ℂ)⟫ := by
            exact
              Representation.groupFunctionPairing_add_left
                (η₁ : H.1 → ℂ) (η₀ : H.1 → ℂ) (ξH : H.1 → ℂ)
    _ = algebraMap ℤ ℂ (n * b₁) + algebraMap ℤ ℂ (n * b₀) := by rw [hb₁, hb₀]
    _ = algebraMap ℤ ℂ (n * (b₁ + b₀)) := by
          rw [← Int.cast_add]
          congr 1
          ring

/-- Helper for Remark 11-11.1-3: the remaining source-faithful endgame is that the explicit local
image term coming from the chosen splitting has all of its linear pairings divisible by `n`. -/
private theorem top_local_image_pairing_divisible_of_residual_family
    (X : Finset (Subgroup G))
    (hXelem : ∀ H : Subgroup G, H ∈ X ↔ IsElementary H)
    (s : ((H : X) → R(H.1)) →ₗ[ℤ] R(G))
    (hs : Function.LeftInverse s (Representation.characterRingRestriction X).toLinearMap)
    {x : (H : X) → R(H.1)} {t : elementary_coherence_target X hXelem} {n : ℤ}
    (hn : n ≠ 0) (hx : s x = 0)
    (hdx : elementary_coherence_defect X hXelem x = n • t)
    (H : X)
    (sH : ((J : (Finset.univ : Finset (Subgroup H.1))) → R(J.1)) →ₗ[ℤ] R(H.1))
    (hsH : Function.LeftInverse sH
      (Representation.characterRingRestriction (Finset.univ : Finset (Subgroup H.1))).toLinearMap)
    (K : Subgroup H.1) (χ : K →* ℂˣ) :
    let XH : Finset (Subgroup H.1) := Finset.univ
    let ψH : (J : XH) → R(J.1) := fun J ↦
      Subgroup.characterRingTransport
        (J.1.equivMapOfInjective H.1.subtype H.1.subtype_injective)
        (x ⟨J.1.map H.1.subtype,
          (hXelem (J.1.map H.1.subtype)).2 <|
            isElementary_of_mulEquiv_local
              (J.1.equivMapOfInjective H.1.subtype H.1.subtype_injective)
              (subgroup_isElementary_of_isElementary_local J.1 ((hXelem H.1).1 H.2))⟩)
    let K0 : XH := ⟨K, by simp [XH]⟩
    ∃ b : ℤ,
      ⟪(χ.toCharacterRing : K → ℂ),
          (((Representation.characterRingRestriction XH) (sH ψH) K0 : R(K)) : K → ℂ)⟫ =
        algebraMap ℤ ℂ (n * b) := by
  classical
  dsimp
  let ξH : R(H.1) := sH ψH
  have hpair_as_induced :
      ⟪(χ.toCharacterRing : K → ℂ),
          (((Representation.characterRingRestriction (Finset.univ : Finset (Subgroup H.1))) ξH
              ⟨K, by simp⟩ : R(K)) : K → ℂ)⟫ =
        ⟪Ind[K](χ.toRepresentation.character), (ξH : H.1 → ℂ)⟫ := by
    -- Package the restriction-to-induced conversion once so the remaining blocker is purely the
    -- source-proof divisibility step on the induced pairing.
    simpa [ξH] using
      (top_local_coordinate_pairing_eq_induced_pairing
        (sH := sH) (ψH := ψH) (K := K) (χ := χ))
  have hHelem : IsElementary H.1 := (hXelem H.1).1 H.2
  have hη :
      Subgroup.characterRingInduction K χ.toCharacterRing ∈ R'(H.1) :=
    induced_linearCharacter_mem_elementaryLinearCharacterSpan_of_subgroup_of_isElementary_local
      K χ hHelem
  obtain ⟨b, hb⟩ :=
    pairing_divisible_of_mem_elementaryLinearCharacterSpan_of_residual_family
      X hXelem s hs hn hx hdx H sH hsH
      (Subgroup.characterRingInduction K χ.toCharacterRing) hη
  refine ⟨b, ?_⟩
  calc
    ⟪(χ.toCharacterRing : K → ℂ),
        (((Representation.characterRingRestriction (Finset.univ : Finset (Subgroup H.1))) ξH
            ⟨K, by simp⟩ : R(K)) : K → ℂ)⟫ =
      ⟪Ind[K](χ.toRepresentation.character), (ξH : H.1 → ℂ)⟫ := hpair_as_induced
    _ = ⟪(((Subgroup.characterRingInduction K χ.toCharacterRing : R(H.1)) : H.1 → ℂ)),
          (ξH : H.1 → ℂ)⟫ := by
          -- The bundled induced character-ring element evaluates to the same induced character.
          simp [Subgroup.characterRingInduction_apply]
    _ = algebraMap ℤ ℂ (n * b) := hb

/-- Helper for Remark 11-11.1-3: the remaining arithmetic step is to show that the residual
`K`-coordinate pairing extracted from the defect identity is divisible by `n` in `ℤ`. -/
private theorem residual_subgroup_pairing_int_divisible_of_defect_multiple
    (X : Finset (Subgroup G))
    (hXelem : ∀ H : Subgroup G, H ∈ X ↔ IsElementary H)
    (s : ((H : X) → R(H.1)) →ₗ[ℤ] R(G))
    (hs : Function.LeftInverse s (Representation.characterRingRestriction X).toLinearMap)
    {x : (H : X) → R(H.1)} {t : elementary_coherence_target X hXelem} {n : ℤ}
    (hn : n ≠ 0) (hx : s x = 0)
    (hdx : elementary_coherence_defect X hXelem x = n • t)
    (H : X) (K : Subgroup H.1) (χ : K →* ℂˣ) :
    let KX : X := ⟨K.map H.1.subtype,
      (hXelem (K.map H.1.subtype)).2 <|
        isElementary_of_mulEquiv_local
          (K.equivMapOfInjective H.1.subtype H.1.subtype_injective)
          (subgroup_isElementary_of_isElementary_local K ((hXelem H.1).1 H.2))⟩
    ∃ m : ℤ, linear_character_pairing_int H.1 K χ (x KX) = n * m := by
  classical
  let KX : X := ⟨K.map H.1.subtype,
    (hXelem (K.map H.1.subtype)).2 <|
      isElementary_of_mulEquiv_local
        (K.equivMapOfInjective H.1.subtype H.1.subtype_injective)
        (subgroup_isElementary_of_isElementary_local K ((hXelem H.1).1 H.2))⟩
  let XH : Finset (Subgroup H.1) := Finset.univ
  let ψH : (J : XH) → R(J.1) := fun J ↦
    Subgroup.characterRingTransport
      (J.1.equivMapOfInjective H.1.subtype H.1.subtype_injective)
      (x ⟨J.1.map H.1.subtype,
        (hXelem (J.1.map H.1.subtype)).2 <|
          isElementary_of_mulEquiv_local
            (J.1.equivMapOfInjective H.1.subtype H.1.subtype_injective)
            (subgroup_isElementary_of_isElementary_local J.1 ((hXelem H.1).1 H.2))⟩)
  let δH : (J : XH) → R(J.1) := fun J ↦
    let JX : X := ⟨J.1.map H.1.subtype,
      (hXelem (J.1.map H.1.subtype)).2 <|
        isElementary_of_mulEquiv_local
          (J.1.equivMapOfInjective H.1.subtype H.1.subtype_injective)
          (subgroup_isElementary_of_isElementary_local J.1 ((hXelem H.1).1 H.2))⟩
    let pJ : elementary_restriction_relation X := ⟨(H, JX), subgroup_chain_map_le_local H.1 J.1⟩
    Subgroup.characterRingTransport
      (J.1.equivMapOfInjective H.1.subtype H.1.subtype_injective)
      (t.1 pJ)
  have htransported :
      ((Representation.characterRingRestriction XH).toLinearMap (x H)) - ψH = n • δH :=
    transported_subgroup_family_defect_eq_zsmul X hXelem hdx H
  obtain ⟨sH, hsH⟩ :=
    characterRingRestriction_has_leftInverse_of_detection_by_restrictions
      (G := H.1) XH subgroup_restriction_detection_on_elementary_group
  let fH : R(H.1) →ₗ[ℤ] ((J : XH) → R(J.1)) := (Representation.characterRingRestriction XH).toLinearMap
  let rH : ((J : XH) → R(J.1)) →ₗ[ℤ] ((J : XH) → R(J.1)) := LinearMap.id - fH.comp sH
  have hresidual : rH ψH = (-n) • rH δH :=
    local_residual_projector_eq_neg_zsmul XH sH hsH htransported
  let K0 : XH := ⟨K, by simp [XH]⟩
  have himage_residual : fH (sH ψH) - ψH = n • rH δH := by
    have hresidual' : ψH - fH (sH ψH) = (-n) • rH δH := by
      simpa [rH, fH, Pi.sub_apply, LinearMap.sub_apply, LinearMap.comp_apply]
        using hresidual
    have hneg := congrArg Neg.neg hresidual'
    simpa [Pi.neg_apply, Pi.smul_apply, zsmul_eq_mul, sub_eq_add_neg, add_comm, add_left_comm,
      add_assoc, mul_comm, mul_left_comm, mul_assoc] using hneg
  obtain ⟨m, hdecomp⟩ :=
    local_residual_pairing_decomposition_of_defect_multiple XH sH hsH himage_residual K0 χ
  have hpair_x :
      algebraMap ℤ ℂ (linear_character_pairing_int H.1 K χ (x KX)) =
        ⟪(χ.toCharacterRing : K → ℂ), (ψH K0 : K → ℂ)⟫ := by
    -- The transported `K`-coordinate of `ψH` is exactly the ambient `KX`-coordinate of `x`.
    simpa [KX, K0, ψH] using
      (subgroup_linear_character_pairing_int_transport_eq H.1 K χ (x KX)).symm
  have hpair_decomp :
      algebraMap ℤ ℂ (linear_character_pairing_int H.1 K χ (x KX)) =
        ⟪(χ.toCharacterRing : K → ℂ),
            (((Representation.characterRingRestriction XH) (sH ψH) K0 : R(K)) : K → ℂ)⟫ +
          algebraMap ℤ ℂ (n * m) := by
    simpa [hpair_x] using hdecomp
  obtain ⟨b, hb⟩ :=
    top_local_image_pairing_divisible_of_residual_family
      X hXelem s hs hn hx hdx H sH hsH K χ
  refine ⟨b + m, ?_⟩
  apply Int.cast_injective
  -- Combine the explicit local-image divisibility with the residual decomposition.
  calc
    algebraMap ℤ ℂ (linear_character_pairing_int H.1 K χ (x KX)) =
        ⟪(χ.toCharacterRing : K → ℂ),
            (((Representation.characterRingRestriction XH) (sH ψH) K0 : R(K)) : K → ℂ)⟫ +
          algebraMap ℤ ℂ (n * m) := hpair_decomp
    _ = algebraMap ℤ ℂ (n * b) + algebraMap ℤ ℂ (n * m) := by rw [hb]
    _ = algebraMap ℤ ℂ ((n * b) + (n * m)) := by simp [Int.cast_add]
    _ = algebraMap ℤ ℂ (n * (b + m)) := by ring

/-- Helper for Remark 11-11.1-3: pairing the `K.map H.subtype` coordinate of a global restriction
family against the transported linear character agrees with the ambient induced pairing. -/
private theorem mapped_linear_character_pairing_eq_induced_global_pairing
    (X : Finset (Subgroup G))
    (hXelem : ∀ H : Subgroup G, H ∈ X ↔ IsElementary H)
    (H : X) (K : Subgroup H.1) (χ : K →* ℂˣ) (ξ : R(G)) :
    let KX : X := ⟨K.map H.1.subtype,
      (hXelem (K.map H.1.subtype)).2 <|
        isElementary_of_mulEquiv_local
          (K.equivMapOfInjective H.1.subtype H.1.subtype_injective)
          (subgroup_isElementary_of_isElementary_local K ((hXelem H.1).1 H.2))⟩
    ⟪((mapped_linear_character_local H.1 K χ).toCharacterRing : KX.1 → ℂ),
        ((Representation.characterRingRestriction X ξ KX : R(KX.1)) : KX.1 → ℂ)⟫ =
      ⟪Ind[KX.1](((mapped_linear_character_local H.1 K χ).toRepresentation.character)),
          (ξ : G → ℂ)⟫ := by
  let KX : X := ⟨K.map H.1.subtype,
    (hXelem (K.map H.1.subtype)).2 <|
      isElementary_of_mulEquiv_local
        (K.equivMapOfInjective H.1.subtype H.1.subtype_injective)
        (subgroup_isElementary_of_isElementary_local K ((hXelem H.1).1 H.2))⟩
  let ξcf : classFunctionSubmodule ℂ G :=
    ⟨(ξ : G → ℂ), by
      -- Global characters are bundled class functions.
      rw [mem_classFunctionSubmodule_iff]
      exact isClassFunction_of_mem_characterRingOverField _ ξ.property⟩
  -- Frobenius reciprocity identifies the local restriction pairing with the ambient induced one.
  simpa [KX, ξcf, Representation.characterRingRestriction_apply] using
    (groupFunctionPairing_induced_linearCharacter_eq_restriction
      (K := KX.1) (α := mapped_linear_character_local H.1 K χ) (x := ξcf)).symm

/-- Helper for Remark 11-11.1-3: after removing the global contribution chosen by `s`, the local
pairing against a transported linear character factors through the range of the coherence defect.
-/
private theorem residual_linear_character_pairing_factors_through_coherence_defect
    (X : Finset (Subgroup G))
    (hXelem : ∀ H : Subgroup G, H ∈ X ↔ IsElementary H)
    (s : ((H : X) → R(H.1)) →ₗ[ℤ] R(G))
    (hs : Function.LeftInverse s (Representation.characterRingRestriction X).toLinearMap)
    (H : X) (K : Subgroup H.1) (χ : K →* ℂˣ) :
    let KX : X := ⟨K.map H.1.subtype,
      (hXelem (K.map H.1.subtype)).2 <|
        isElementary_of_mulEquiv_local
          (K.equivMapOfInjective H.1.subtype H.1.subtype_injective)
          (subgroup_isElementary_of_isElementary_local K ((hXelem H.1).1 H.2))⟩
    ∃ F : LinearMap.range (elementary_coherence_defect X hXelem) →ₗ[ℤ] ℂ,
      ∀ ψ : (J : X) → R(J.1),
        F ((elementary_coherence_defect X hXelem).rangeRestrict ψ) =
          ⟪((mapped_linear_character_local H.1 K χ).toCharacterRing : KX.1 → ℂ),
              (ψ KX : KX.1 → ℂ)⟫ -
            ⟪Ind[KX.1](((mapped_linear_character_local H.1 K χ).toRepresentation.character)),
                (s ψ : G → ℂ)⟫ := by
  let L : Type := (J : X) → R(J.1)
  let f : R(G) →ₗ[ℤ] L := (Representation.characterRingRestriction X).toLinearMap
  let d : L →ₗ[ℤ] elementary_coherence_target X hXelem := elementary_coherence_defect X hXelem
  let KX : X := ⟨K.map H.1.subtype,
    (hXelem (K.map H.1.subtype)).2 <|
      isElementary_of_mulEquiv_local
        (K.equivMapOfInjective H.1.subtype H.1.subtype_injective)
        (subgroup_isElementary_of_isElementary_local K ((hXelem H.1).1 H.2))⟩
  obtain ⟨q, hq⟩ :=
    characterRingRestriction_residual_factors_through_coherence_defect X hXelem s hs
  let pairingLinear : R(KX.1) →ₗ[ℤ] ℂ :=
    { toFun := fun η ↦
        ⟪((mapped_linear_character_local H.1 K χ).toCharacterRing : KX.1 → ℂ),
            (η : KX.1 → ℂ)⟫
      map_add' := by
        intro η θ
        simpa using
          (Representation.groupFunctionPairing_add_right
            (((mapped_linear_character_local H.1 K χ).toCharacterRing : R(KX.1)) : KX.1 → ℂ)
            (η : KX.1 → ℂ) (θ : KX.1 → ℂ))
      map_smul' := by
        intro n η
        simpa [zsmul_eq_mul] using
          (Representation.groupFunctionPairing_smul_right
            (a := (n : ℂ))
            (φ := (((mapped_linear_character_local H.1 K χ).toCharacterRing : R(KX.1)) :
              KX.1 → ℂ))
            (ψ := (η : KX.1 → ℂ))).symm }
  let coordPair : L →ₗ[ℤ] ℂ :=
    pairingLinear.comp (LinearMap.proj (R := ℤ) (φ := fun J : X ↦ R(J.1)) KX)
  let F : LinearMap.range d →ₗ[ℤ] ℂ := coordPair.comp q
  refine ⟨F, fun ψ ↦ ?_⟩
  have hqψ : q (d.rangeRestrict ψ) = ψ - f (s ψ) := by
    exact LinearMap.congr_fun hq ψ
  have hglobal :
      coordPair (f (s ψ)) =
        ⟪Ind[KX.1](((mapped_linear_character_local H.1 K χ).toRepresentation.character)),
            (s ψ : G → ℂ)⟫ := by
    -- The `KX`-coordinate of a genuine global restriction family is measured by ambient induction.
    simpa [coordPair, f] using
      mapped_linear_character_pairing_eq_induced_global_pairing
        X hXelem H K χ (s ψ)
  -- Evaluate the residual projector identity at `ψ` and then pair the `KX`-coordinate.
  calc
    F (d.rangeRestrict ψ) = coordPair (q (d.rangeRestrict ψ)) := rfl
    _ = coordPair (ψ - f (s ψ)) := by rw [hqψ]
    _ = coordPair ψ - coordPair (f (s ψ)) := by
          simp [coordPair]
    _ = ⟪((mapped_linear_character_local H.1 K χ).toCharacterRing : KX.1 → ℂ),
            (ψ KX : KX.1 → ℂ)⟫ -
          ⟪Ind[KX.1](((mapped_linear_character_local H.1 K χ).toRepresentation.character)),
              (s ψ : G → ℂ)⟫ := by
          simp [coordPair, hglobal]

/-- Helper for Remark 11-11.1-3: on an elementary finite group, integrality of all linear
pairings on subgroups extends by linearity to every monomial character. -/
private theorem pairing_mem_range_of_mem_monomialCharacterSpan_on_elementary_group
    {H : Type} [Group H] [Finite H]
    (φ : classFunctionSubmodule ℂ H)
    (hpair : ∀ (K : Subgroup H) (_ : IsElementary K) (χ : K →* ℂˣ),
      ⟪χ.toCharacterRing, Subgroup.classFunctionRestriction K φ⟫ ∈ Set.range (algebraMap ℤ ℂ))
    (hH : IsElementary H)
    {η : R(H)} (hη : η ∈ monomialCharacterSpan H) :
    ⟪(η : H → ℂ), (φ : H → ℂ)⟫ ∈ Set.range (algebraMap ℤ ℂ) := by
  rw [monomialCharacterSpan] at hη
  -- Extend the degree-`1` pairing hypothesis from the generators to the whole monomial span.
  induction hη using Submodule.span_induction with
  | mem ξ hξ =>
      rcases hξ with ⟨K, α, hα⟩
      rw [← hα]
      rw [groupFunctionPairing_induced_linearCharacter_eq_restriction]
      exact hpair K (subgroup_isElementary_of_isElementary_local K hH) α
  | zero =>
      refine ⟨0, ?_⟩
      simp [Representation.groupFunctionPairingOverField]
  | add ξ ζ _ _ hξ hζ =>
      rcases hξ with ⟨a, ha⟩
      rcases hζ with ⟨b, hb⟩
      refine ⟨a + b, ?_⟩
      simpa [Representation.groupFunctionPairing_add_left, ha, hb, map_add]
  | smul n ξ _ hξ =>
      rcases hξ with ⟨a, ha⟩
      refine ⟨n * a, ?_⟩
      calc
        algebraMap ℤ ℂ (n * a) =
            (n : ℂ) * ⟪(ξ : H → ℂ), (φ : H → ℂ)⟫ := by
              simpa [ha, Int.cast_mul]
        _ = ⟪((n : ℤ) • (ξ : H → ℂ)), (φ : H → ℂ)⟫ := by
              simpa using
                (Representation.groupFunctionPairing_smul_left
                  (a := (n : ℂ)) (φ := (ξ : H → ℂ)) (ψ := (φ : H → ℂ)))
        _ = ⟪((n • ξ : R(H)) : H → ℂ), (φ : H → ℂ)⟫ := by
              rfl

/-- Helper for Remark 11-11.1-3: on an elementary finite group, a class function is integral as
soon as all of its linear pairings on elementary subgroups are integers. -/
private theorem integer_pairing_criterion_for_characterRing_on_elementary_subgroups
    {H : Type} [Group H] [Finite H]
    (hH : IsElementary H)
    (φ : classFunctionSubmodule ℂ H)
    (hpair : ∀ (K : Subgroup H) (_ : IsElementary K) (χ : K →* ℂˣ),
      ⟪χ.toCharacterRing, Subgroup.classFunctionRestriction K φ⟫ ∈ Set.range (algebraMap ℤ ℂ)) :
    (φ : H → ℂ) ∈ R(H) := by
  classical
  let _ : NeZero (Nat.card H : ℂ) := ⟨by
    exact_mod_cast Nat.card_pos.ne'⟩
  obtain ⟨ι, _, π, hπ_pairwise, hπ_complete⟩ :=
    FDRep.exists_complete_pairwise_nonisomorphic_simple_family (k := ℂ) (G := H)
  let b := irreducibleCharacters_basis_of_classFunctionSubspace_of_complete_family
    π hπ_pairwise hπ_complete
  have hsum_fun :
      (∑ i, ((((b.repr φ i) • b i : classFunctionSubmodule ℂ H) : H → ℂ))) ∈ R(H) := by
    -- Expand `φ` in the irreducible basis and show each coefficient is an integer.
    refine Submodule.sum_mem (R(H)) ?_
    intro i hi
    have hmono : fdRepCharacterRing (π i) ∈ monomialCharacterSpan H := by
      rw [monomialCharacterSpan_eq_top_of_isElementary hH]
      simp
    have hpairing :
        ⟪((fdRepCharacterRing (π i) : R(H)) : H → ℂ), (φ : H → ℂ)⟫ ∈
          Set.range (algebraMap ℤ ℂ) :=
      pairing_mem_range_of_mem_monomialCharacterSpan_on_elementary_group
        φ hpair hH hmono
    rcases hpairing with ⟨a, ha⟩
    have hcoeff : b.repr φ i = algebraMap ℤ ℂ a := by
      calc
        b.repr φ i =
            Representation.groupFunctionPairingOverField ℂ (φ : H → ℂ) (π i).character :=
          repr_irreducible_character_basis_eq_pairing_local
            (π := π) hπ_pairwise hπ_complete φ i
        _ = algebraMap ℤ ℂ a := by
          simpa [fdRepCharacterRing, Representation.groupFunctionPairing_comm] using ha
    have hb :
        (((b i : classFunctionSubmodule ℂ H) : H → ℂ)) ∈ R(H) := by
      have hb_eq :
          (((b i : classFunctionSubmodule ℂ H) : H → ℂ)) =
            (((fdRepCharacterRing (π i) : R(H)) : H → ℂ)) := by
        ext h
        simp [b, irreducibleCharacters_basis_of_classFunctionSubspace_of_complete_family_apply]
      rw [hb_eq]
      exact (fdRepCharacterRing (π i)).property
    have hterm :
        ((((b.repr φ i) • b i : classFunctionSubmodule ℂ H) : H → ℂ)) =
          a • (((b i : classFunctionSubmodule ℂ H) : H → ℂ)) := by
      ext h
      simp [hcoeff]
    rw [hterm]
    exact (R(H)).smul_mem a hb
  have hsum_coe :
      (∑ i, ((((b.repr φ i) • b i : classFunctionSubmodule ℂ H) : H → ℂ))) =
        ((((∑ i, ((b.repr φ i) • b i : classFunctionSubmodule ℂ H)) :
            classFunctionSubmodule ℂ H) : H → ℂ)) := by
    ext h
    let eval_h : classFunctionSubmodule ℂ H →ₗ[ℂ] ℂ :=
      { toFun := fun z ↦ z h
        map_add' := by
          intro y z
          rfl
        map_smul' := by
          intro a z
          rfl }
    simpa using
      (_root_.map_sum eval_h
        (fun j ↦ ((b.repr φ j) • b j : classFunctionSubmodule ℂ H)) Finset.univ).symm
  have hφ :
      ((((∑ i, ((b.repr φ i) • b i : classFunctionSubmodule ℂ H)) :
          classFunctionSubmodule ℂ H) : H → ℂ)) = (φ : H → ℂ) := by
    exact congrArg (fun z : classFunctionSubmodule ℂ H ↦ (z : H → ℂ)) (b.sum_repr φ)
  -- Replace the basis expansion by the original class function.
  exact hφ.symm ▸ (hsum_coe.symm ▸ hsum_fun)

/-- Helper for Remark 11-11.1-3: once a chosen restriction splitting removes the global part,
the scaled residual coordinate belongs to the local character ring. -/
private theorem scaled_residual_coordinate_mem_characterRing
    (X : Finset (Subgroup G))
    (hXelem : ∀ H : Subgroup G, H ∈ X ↔ IsElementary H)
    (s : ((H : X) → R(H.1)) →ₗ[ℤ] R(G))
    (hs : Function.LeftInverse s (Representation.characterRingRestriction X).toLinearMap)
    {x : (H : X) → R(H.1)} {t : elementary_coherence_target X hXelem} {n : ℤ}
    (hn : n ≠ 0) (hx : s x = 0)
    (hdx : elementary_coherence_defect X hXelem x = n • t)
    (H : X) :
    (fun h : H.1 ↦ ((x H : H.1 → ℂ) h) / (n : ℂ)) ∈ R(H.1) := by
  have hHelem : IsElementary H.1 := (hXelem H.1).1 H.2
  let φH : classFunctionSubmodule ℂ H.1 :=
    ⟨fun h : H.1 ↦ ((x H : H.1 → ℂ) h) / (n : ℂ), by
      -- Scaling a class function preserves the class-function submodule.
      rw [show (fun h : H.1 ↦ ((x H : H.1 → ℂ) h) / (n : ℂ)) =
          ((n : ℂ)⁻¹ • ((x H : R(H.1)) : H.1 → ℂ)) by
            ext h
            simp [div_eq_mul_inv, mul_comm]]
      have hxClass :
          (((x H : R(H.1)) : H.1 → ℂ)) ∈ classFunctionSubmodule ℂ H.1 := by
        rw [mem_classFunctionSubmodule_iff]
        exact isClassFunction_of_mem_characterRingOverField _ (x H).property
      exact (classFunctionSubmodule ℂ H.1).smul_mem ((n : ℂ)⁻¹) hxClass⟩
  refine integer_pairing_criterion_for_characterRing_on_elementary_subgroups hHelem φH ?_
  intro K hKelem χ
  have hKmapElem : IsElementary (K.map H.1.subtype) := by
    exact
      isElementary_of_mulEquiv_local
        (K.equivMapOfInjective H.1.subtype H.1.subtype_injective) hKelem
  have hKmap_mem : K.map H.1.subtype ∈ X := (hXelem (K.map H.1.subtype)).2 hKmapElem
  let KX : X := ⟨K.map H.1.subtype, hKmap_mem⟩
  have hKXle : KX.1 ≤ H.1 := subgroup_chain_map_le_local H.1 K
  let p : elementary_restriction_relation X := ⟨(H, KX), hKXle⟩
  have hp_defect :
      ((Subgroup.characterRingRestrictionOfLe hKXle) (x H) : R(KX.1)) - x KX = n • t.1 p := by
    -- The first defect coordinate at `(H, KX)` records the nested restriction equation.
    have hp := congrFun (congrArg Prod.fst hdx) p
    simpa [elementary_coherence_defect, p] using hp
  have hpair_t :
      ⟪((mapped_linear_character_local H.1 K χ).toCharacterRing : KX.1 → ℂ),
          (t.1 p : KX.1 → ℂ)⟫ ∈ Set.range (algebraMap ℤ ℂ) := by
    -- The defect coordinate is an honest character-ring element, so its linear pairing is integral.
    exact
      pairing_mem_range_int_of_mem_characterRing_with_linear_character_local
        (η := t.1 p) (χ := mapped_linear_character_local H.1 K χ)
  rcases hpair_t with ⟨a, ha⟩
  obtain ⟨m, hm⟩ :=
    residual_subgroup_pairing_int_divisible_of_defect_multiple
      X hXelem s hs hn hx hdx H K χ
  have hpair_x :
      ⟪((mapped_linear_character_local H.1 K χ).toCharacterRing : KX.1 → ℂ),
          (x KX : KX.1 → ℂ)⟫ =
        algebraMap ℤ ℂ (n * m) := by
    -- The new blocker has been isolated to an explicit integer divisibility statement.
    calc
      ⟪((mapped_linear_character_local H.1 K χ).toCharacterRing : KX.1 → ℂ),
          (x KX : KX.1 → ℂ)⟫ =
        algebraMap ℤ ℂ (linear_character_pairing_int H.1 K χ (x KX)) := by
          symm
          exact linear_character_pairing_int_spec H.1 K χ (x KX)
      _ = algebraMap ℤ ℂ (n * m) := by
          rw [hm]
  have hp_defect' :
      ((Subgroup.characterRingRestrictionOfLe hKXle) (x H) : R(KX.1)) =
        x KX + n • t.1 p := by
    -- Repackage the defect coordinate as an additive decomposition.
    exact eq_add_of_sub_eq hp_defect
  have hpair_mapped_restriction :
      ⟪((mapped_linear_character_local H.1 K χ).toCharacterRing : KX.1 → ℂ),
          (((Subgroup.characterRingRestrictionOfLe hKXle) (x H) : R(KX.1)) :
            KX.1 → ℂ)⟫ =
        algebraMap ℤ ℂ (n * m + n * a) := by
    -- Pair the defect decomposition with the transported linear character on `KX`.
    calc
      ⟪((mapped_linear_character_local H.1 K χ).toCharacterRing : KX.1 → ℂ),
          (((Subgroup.characterRingRestrictionOfLe hKXle) (x H) : R(KX.1)) :
            KX.1 → ℂ)⟫ =
        ⟪((mapped_linear_character_local H.1 K χ).toCharacterRing : KX.1 → ℂ),
            ((x KX + n • t.1 p : R(KX.1)) : KX.1 → ℂ)⟫ := by
          rw [hp_defect']
      _ = ⟪((mapped_linear_character_local H.1 K χ).toCharacterRing : KX.1 → ℂ),
            (x KX : KX.1 → ℂ)⟫ +
          ⟪((mapped_linear_character_local H.1 K χ).toCharacterRing : KX.1 → ℂ),
            ((n • t.1 p : R(KX.1)) : KX.1 → ℂ)⟫ := by
          exact
            Representation.groupFunctionPairing_add_right
              (((mapped_linear_character_local H.1 K χ).toCharacterRing : R(KX.1)) :
                KX.1 → ℂ)
              (x KX : KX.1 → ℂ)
              ((n • t.1 p : R(KX.1)) : KX.1 → ℂ)
      _ = algebraMap ℤ ℂ (n * m) +
          ⟪((mapped_linear_character_local H.1 K χ).toCharacterRing : KX.1 → ℂ),
            ((n • t.1 p : R(KX.1)) : KX.1 → ℂ)⟫ := by
          rw [hpair_x]
      _ = algebraMap ℤ ℂ (n * m) + (n : ℂ) *
          ⟪((mapped_linear_character_local H.1 K χ).toCharacterRing : KX.1 → ℂ),
              (t.1 p : KX.1 → ℂ)⟫ := by
          simpa [zsmul_eq_mul] using
            (Representation.groupFunctionPairing_smul_right
              (a := (n : ℂ))
              (φ := (((mapped_linear_character_local H.1 K χ).toCharacterRing :
                R(KX.1)) : KX.1 → ℂ))
              (ψ := (t.1 p : KX.1 → ℂ))).symm
      _ = algebraMap ℤ ℂ (n * m) + (n : ℂ) * algebraMap ℤ ℂ a := by
          rw [ha]
      _ = algebraMap ℤ ℂ (n * m + n * a) := by
          simp [Int.cast_add, Int.cast_mul, mul_add, mul_assoc]
  have hpair_local_restriction :
      ⟪(χ.toCharacterRing : K → ℂ), fun k : K ↦ ((x H : H.1 → ℂ) k)⟫ =
        algebraMap ℤ ℂ (n * m + n * a) := by
    -- Transport the `KX`-pairing back to the original subgroup `K`.
    calc
      ⟪(χ.toCharacterRing : K → ℂ), (((K ↾R[ℂ]) (x H) : R(K)) : K → ℂ)⟫ =
        ⟪((mapped_linear_character_local H.1 K χ).toCharacterRing : KX.1 → ℂ),
            (((Subgroup.characterRingRestrictionOfLe hKXle) (x H) : R(KX.1)) :
              KX.1 → ℂ)⟫ := by
          symm
          rw [linear_character_pairing_transport_eq H.1 K χ
            ((Subgroup.characterRingRestrictionOfLe hKXle) (x H))]
          rw [mapped_coordinate_transport_eq_local_restriction H.1 K (x H)]
      _ = algebraMap ℤ ℂ (n * m + n * a) := hpair_mapped_restriction
    -- Forget the bundled restriction and view it as the original restricted class function.
    simpa [Subgroup.characterRingRestriction_apply]
  have hrestrict_scaled :
      (Subgroup.classFunctionRestriction K φH : K → ℂ) =
        (n : ℂ)⁻¹ • fun k : K ↦ ((x H : H.1 → ℂ) k) := by
    ext k
    -- Restricting the divided coordinate is the same as dividing the restricted coordinate.
    simp [φH, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]
  have hnC : (n : ℂ) ≠ 0 := by
    exact_mod_cast hn
  have hpair_scaled :
      ⟪(χ.toCharacterRing : K → ℂ), (Subgroup.classFunctionRestriction K φH : K → ℂ)⟫ =
        algebraMap ℤ ℂ (m + a) := by
    -- Divide the already-integral pairing identity by the nonzero scalar `n`.
    calc
      ⟪(χ.toCharacterRing : K → ℂ), (Subgroup.classFunctionRestriction K φH : K → ℂ)⟫ =
        (n : ℂ)⁻¹ *
          ⟪(χ.toCharacterRing : K → ℂ), fun k : K ↦ ((x H : H.1 → ℂ) k)⟫ := by
            rw [hrestrict_scaled]
            simpa [Algebra.smul_def] using
              (Representation.groupFunctionPairing_smul_right
                (a := (n : ℂ)⁻¹)
                (φ := (χ.toCharacterRing : K → ℂ))
                (ψ := fun k : K ↦ ((x H : H.1 → ℂ) k)))
      _ = (n : ℂ)⁻¹ * algebraMap ℤ ℂ (n * m + n * a) := by
            rw [hpair_local_restriction]
      _ = algebraMap ℤ ℂ (m + a) := by
            have hcast :
                algebraMap ℤ ℂ (n * m + n * a) =
                  (n : ℂ) * algebraMap ℤ ℂ (m + a) := by
              simp [Int.cast_add, Int.cast_mul, mul_add, mul_assoc]
            rw [hcast]
            simp [hnC, mul_assoc]
  exact ⟨m + a, hpair_scaled.symm⟩

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
  refine ⟨fun H ↦
    ⟨fun h : H.1 ↦ ((x H : H.1 → ℂ) h) / (n : ℂ),
      scaled_residual_coordinate_mem_characterRing X hXelem s hs hn hx hdx H⟩, ?_⟩
  ext H h
  have hnC : (n : ℂ) ≠ 0 := by
    exact_mod_cast hn
  -- The chosen coordinatewise division multiplies back to the original local character.
  change (n : ℂ) * (((x H : H.1 → ℂ) h) / (n : ℂ)) = ((x H : H.1 → ℂ) h)
  rw [div_eq_mul_inv]
  ring_nf
  simp [hnC]

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
    residual_family_divisible_of_multiple_coherence_defect X hXelem s hs hn hx hdx
  refine ⟨y, ?_⟩
  -- Apply the defect map to `n • y = x` and cancel `n` in the defect target.
  have hny : n • elementary_coherence_defect X hXelem y = n • t := by
    calc
      n • elementary_coherence_defect X hXelem y = elementary_coherence_defect X hXelem x := by
        simpa using congrArg (elementary_coherence_defect X hXelem) hy
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

-- Building a basis for the torsion-free quotient triggers expensive module-instance search.
set_option maxHeartbeats 5000000 in
set_option synthInstance.maxHeartbeats 2000000 in
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
  let T : Type := elementary_coherence_target X hXelem
  let d : ((H : X) → R(H.1)) →ₗ[ℤ] T := elementary_coherence_defect X hXelem
  let q : T →ₗ[ℤ] T ⧸ LinearMap.range d := (LinearMap.range d).mkQ
  letI : Module.Finite ℤ T := elementary_coherence_target_moduleFinite X hXelem
  have hquot : Module.IsTorsionFree ℤ (T ⧸ LinearMap.range d) := by
    -- Saturation of the defect image is exactly the torsion-free quotient input for splitting.
    simpa [T, d] using elementary_coherence_defect_cokernel_torsion_free X hXelem
  letI : Module.IsTorsionFree ℤ (T ⧸ LinearMap.range d) := hquot
  letI : Module.Finite ℤ (T ⧸ LinearMap.range d) :=
    Module.Finite.of_surjective q (Submodule.mkQ_surjective _)
  obtain ⟨n, b⟩ :
      Σ n, Module.Basis (Fin n) ℤ (T ⧸ LinearMap.range d) :=
    Module.basisOfFiniteTypeTorsionFree'
  letI : Module.Projective ℤ (T ⧸ LinearMap.range d) := Module.Projective.of_basis b
  obtain ⟨t, ht⟩ :=
    Module.projective_lifting_property q (LinearMap.id : _ →ₗ[ℤ] _)
      (Submodule.mkQ_surjective _)
  let p : T →ₗ[ℤ] T := LinearMap.id - t.comp q
  have ht_apply :
      ∀ z : T ⧸ LinearMap.range d, q (t z) = z := by
    intro z
    have hEval := congrArg
      (fun g : (T ⧸ LinearMap.range d) →ₗ[ℤ] (T ⧸ LinearMap.range d) ↦ g z) ht
    simpa using hEval
  have hp_range : ∀ y : T, p y ∈ LinearMap.range d := by
    intro y
    rw [← Submodule.ker_mkQ (LinearMap.range d), LinearMap.mem_ker]
    -- The quotient projector kills the quotient coordinate, so the complement lands in the range.
    change q y - q (t (q y)) = 0
    rw [ht_apply (q y), sub_self]
  letI : Module ℤ ↥(LinearMap.range d) := (LinearMap.range d).module
  let pRange := LinearMap.codRestrict (LinearMap.range d) p hp_range
  refine ⟨pRange, ?_⟩
  intro x
  have hqx : q (((LinearMap.range d).subtype) x) = 0 := by
    exact (Submodule.Quotient.mk_eq_zero (LinearMap.range d)).2 x.property
  have hpfix : p (((LinearMap.range d).subtype) x) = ((LinearMap.range d).subtype) x := by
    change ((LinearMap.range d).subtype x) -
        t (q (((LinearMap.range d).subtype) x)) =
      ((LinearMap.range d).subtype x)
    rw [hqx]
    simp
  -- On the actual range, the complementary projector is the identity.
  exact Subtype.ext hpfix

/-- Helper for Remark 11-11.1-3: once the integral coherence-defect cokernel is torsion-free, the
base-changed inclusion of its range stays injective. -/
private theorem elementary_coherence_defect_range_subtype_baseChange_injective
    (X : Finset (Subgroup G))
    (hXelem : ∀ H : Subgroup G, H ∈ X ↔ IsElementary H) :
    Function.Injective
      ((((LinearMap.range (elementary_coherence_defect X hXelem)).subtype).baseChange A) :
        TensorProduct ℤ A (LinearMap.range (elementary_coherence_defect X hXelem)) →ₗ[A]
          TensorProduct ℤ A (elementary_coherence_target X hXelem)) := by
  obtain ⟨r, hr⟩ := elementary_coherence_defect_range_subtype_split X hXelem
  -- Base change now preserves injectivity because the integral range inclusion already splits.
  exact
    Representation.baseChange_injective_of_leftInverse
      (A := A) ((LinearMap.range (elementary_coherence_defect X hXelem)).subtype) r hr

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
private theorem tensor_rangeRestrict_eq_zero_of_tensor_coherence_defect_eq_zero
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
  have hi :
      Function.Injective i :=
    elementary_coherence_defect_range_subtype_baseChange_injective (A := A) X hXelem
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
set_option maxHeartbeats 5000000 in
set_option synthInstance.maxHeartbeats 2000000 in
/-- Remark 11-11.1-3: if `X` is exactly the finite family of elementary subgroups of `G`, then a
coherent family of local elements `φ_H ∈ A ⊗ R(H)` on `X`, compatible with the canonical
restriction and conjugation-transport maps on tensor character rings, comes from a unique global
tensor character `φ ∈ A ⊗ R(G)`. This statement is purely ring-linear in `A`; no ambient complex
realization structure on `A` belongs to the public API. -/
theorem existsUnique_global_tensorCharacterRing_of_coherent_family_on_elementarySubgroups
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
    ∃! φ : A ⊗R(G),
      ∀ H : X, Subgroup.tensorCharacterRingRestriction (A := A) H.1 φ = φX H := by
  classical
  let L : Type := (H : X) → R(H.1)
  let T : Type := elementary_coherence_target X hXelem
  let f : R(G) →ₗ[ℤ] L := (Representation.characterRingRestriction X).toLinearMap
  let d : L →ₗ[ℤ] T := elementary_coherence_defect X hXelem
  have hdetect :
      ∀ φ : classFunctionSubmodule ℂ G,
        (∀ H : X, (H.1.classFunctionRestriction φ : H.1 → ℂ) ∈ R(H.1)) →
          (φ : G → ℂ) ∈ R(G) := by
    intro φ hφ
    exact
      Representation.classFunction_mem_characterRing_of_restrict_mem_on_elementarySubgroups
        X hXelem φ hφ
  obtain ⟨s, hs⟩ :=
    characterRingRestriction_has_leftInverse_of_detection_by_restrictions X hdetect
  obtain ⟨q, hq⟩ :=
    characterRingRestriction_residual_factors_through_coherence_defect X hXelem s hs
  have hscomp : s.comp f = (LinearMap.id : R(G) →ₗ[ℤ] R(G)) := by
    exact LinearMap.ext hs
  let E : TensorProduct ℤ A L ≃ₗ[A] ((H : X) → A ⊗R(H.1)) :=
    tensorCharacterRingRestrictionFamilyEquiv (A := A) X
  let C :
      TensorProduct ℤ A T ≃ₗ[A] tensorElementaryCoherenceTarget (A := A) X hXelem :=
    tensorElementaryCoherenceEquiv (A := A) X hXelem
  let fA : TensorProduct ℤ A (R(G)) →ₗ[A] TensorProduct ℤ A L := f.baseChange A
  let dA : TensorProduct ℤ A L →ₗ[A] TensorProduct ℤ A T := d.baseChange A
  let dr : L →ₗ[ℤ] LinearMap.range d := d.rangeRestrict
  let drA :
      TensorProduct ℤ A L →ₗ[A] TensorProduct ℤ A (LinearMap.range d) :=
    dr.baseChange A
  let sA :
      TensorProduct ℤ A L →ₗ[A] TensorProduct ℤ A (R(G)) := s.baseChange A
  let qA :
      TensorProduct ℤ A (LinearMap.range d) →ₗ[A] TensorProduct ℤ A L := q.baseChange A
  let F :
      TensorProduct ℤ A (R(G)) →ₗ[A] ((H : X) → A ⊗R(H.1)) :=
    LinearMap.pi fun H : X ↦ Subgroup.tensorCharacterRingRestriction (A := A) H.1
  have hFA : F = E.toLinearMap.comp fA := by
    simpa [E, F, fA] using tensor_characterRingRestriction_family_eq_baseChange (A := A) X
  have hsA :
      sA.comp fA =
        (LinearMap.id : TensorProduct ℤ A (R(G)) →ₗ[A] TensorProduct ℤ A (R(G))) := by
    simpa [fA, sA, LinearMap.baseChange_comp] using congrArg (LinearMap.baseChange A) hscomp
  let y : TensorProduct ℤ A L :=
    E.symm φX
  have hcoh :
      tensorElementaryCoherenceDefect (A := A) X hXelem φX =
        ((fun _ => 0), fun _ => 0) := by
    exact
      tensorElementaryCoherenceDefect_eq_zero_of_coherent_family
        (A := A) X hXelem φX hres hconj
  have hCA :
      tensorElementaryCoherenceDefect (A := A) X hXelem =
        (C.toLinearMap.comp dA).comp E.symm.toLinearMap := by
    simpa [C, dA, E] using
      tensorElementaryCoherenceDefect_eq_baseChange (A := A) X hXelem
  have hdA0 : d.baseChange A y = 0 := by
    have hyCA :
        tensorElementaryCoherenceDefect (A := A) X hXelem φX = C (dA y) := by
      simpa [hCA, y, C, dA, E, LinearMap.comp_apply] using
        congrArg (fun m => m φX) hCA
    have : dA y = 0 := by
      apply C.injective
      calc
        C (dA y) = tensorElementaryCoherenceDefect (A := A) X hXelem φX := hyCA.symm
        _ = ((fun _ => 0), fun _ => 0) := hcoh
        _ = C 0 := by
          change ((fun _ => 0), fun _ => 0) = ((fun _ => 0), fun _ => 0)
          rfl
    simpa [dA] using this
  let S :
      ((H : X) → A ⊗R(H.1)) →ₗ[A] TensorProduct ℤ A (R(G)) :=
    sA.comp E.symm.toLinearMap
  have hqA :
      qA.comp drA =
        (LinearMap.id : TensorProduct ℤ A L →ₗ[A] TensorProduct ℤ A L) - fA.comp sA := by
    -- Base change transports the integral residual-factorization unchanged.
    simpa [drA, qA, fA, sA, LinearMap.baseChange_comp] using
      congrArg (LinearMap.baseChange A) hq
  have hResidualTransport :
      (E.toLinearMap.comp (qA.comp drA)).comp E.symm.toLinearMap =
        (LinearMap.id : ((H : X) → A ⊗R(H.1)) →ₗ[A] ((H : X) → A ⊗R(H.1))) - F.comp S := by
    -- Transport the residual projector from `TensorProduct ℤ A L` to the actual tensor family
    -- space indexed by the elementary subgroups.
    apply LinearMap.ext
    intro ψ
    have hEval := congrArg (fun m => E (m (E.symm ψ))) hqA
    simpa [S, F, hFA, LinearMap.comp_apply] using hEval
  have hcohRange :
      (tensorElementaryCoherenceDefect (A := A) X hXelem).rangeRestrict φX = 0 := by
    -- Coherence kills the tensor defect even after passing to its actual range.
    exact
      tensor_coherence_defect_rangeRestrict_eq_zero_of_coherent_family
        (A := A) X hXelem φX hres hconj
  have hfamily :
      F (S φX) = φX := by
    -- Route correction: the failed quotient route tried to kill the residual class directly in
    -- `A ⊗ (L / range f)`. The corrected source-faithful bridge first proves that the
    -- base-changed range inclusion for the integral coherence defect is injective, so `hdA0`
    -- already forces `drA y = 0`.
    have hdrA0 : drA y = 0 := by
      simpa [drA] using
        tensor_rangeRestrict_eq_zero_of_tensor_coherence_defect_eq_zero
          (A := A) X hXelem (y := y) hdA0
    have hResidualEval :
        E (qA (drA y)) = φX - F (S φX) := by
      simpa [S, y, LinearMap.comp_apply] using congrArg (fun m => m φX) hResidualTransport
    have hdiff : φX - F (S φX) = 0 := by
      calc
        φX - F (S φX) = E (qA (drA y)) := hResidualEval.symm
        _ = 0 := by simp [hdrA0]
    exact (sub_eq_zero.mp hdiff).symm
  refine ⟨S φX, ?_, ?_⟩
  · intro H
    exact congrFun hfamily H
  · intro ψ hψ
    have hfamilyψ : F ψ = F (S φX) := by
      ext H
      calc
        F ψ H = φX H := by
          simpa [F] using hψ H
        _ = F (S φX) H := by
          simpa [S, y] using (congrFun hfamily H).symm
    have hEqBase : fA ψ = fA (S φX) := by
      apply E.injective
      calc
        E (fA ψ) = F ψ := by
          symm
          simpa [hFA, LinearMap.comp_apply]
        _ = F (S φX) := hfamilyψ
        _ = E (fA (S φX)) := by
          simpa [hFA, LinearMap.comp_apply]
    have hsAψ :
        sA (fA ψ) = ψ := by
      simpa [LinearMap.comp_apply] using congrArg (fun m => m ψ) hsA
    have hsAφ :
        sA (fA (S φX)) = S φX := by
      simpa [S, y, LinearMap.comp_apply] using congrArg (fun m => m (S φX)) hsA
    calc
      ψ = sA (fA ψ) := hsAψ.symm
      _ = sA (fA (S φX)) := by
            rw [hEqBase]
      _ = S φX := hsAφ

end CharacterizationOfCharacters

end Representation
