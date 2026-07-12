import Mathlib
import LinearRepresentations_Serre_1977.Chap10.Definition_10_10_1_3
import LinearRepresentations_Serre_1977.Chap11.Remark_11_11_1_3.Brauer.Main
import LinearRepresentations_Serre_1977.RepresentationTheory.FrobeniusCharacterPairing
import LinearRepresentations_Serre_1977.Chap11.Remark_11_11_1_3.TensorCharacterRingRestriction
import LinearRepresentations_Serre_1977.Chap11.Remark_11_11_1_3.RestrictionFamily
import LinearRepresentations_Serre_1977.Chap11.Remark_11_11_1_3.ElementaryConjugation
import LinearRepresentations_Serre_1977.Chap11.Remark_11_11_1_3.ElementaryDetection
import LinearRepresentations_Serre_1977.Chap11.Remark_11_11_1_3.IntegralRestrictionSplitting
import LinearRepresentations_Serre_1977.Chap11.Remark_11_11_1_3.ElementaryCoherence
import LinearRepresentations_Serre_1977.Chap11.Remark_11_11_1_3.SubgroupLinearPairing

noncomputable section

universe v

namespace Representation

section CharacterizationOfCharacters

open scoped Pointwise Representation SubgroupInduction TensorProduct

variable {G : Type} [Group G] [Finite G]
variable {A : Type v} [CommRing A]

local notation:max s " •ᶜ " H => (MulAut.conj s • H : Subgroup G)

/-- Helper for Remark 11-11.1-3: every subgroup of a finite group is finite. -/
local instance fintypeHelperLocalTopLocalPairing1 (H : Subgroup G) : Fintype H := Fintype.ofFinite H

/-- Helper for Remark 11-11.1-3: the remaining arithmetic step is to show that the residual
`K`-coordinate pairing extracted from the defect identity is divisible by `n` in `ℤ`. -/
theorem top_local_image_restriction_eq_coordinate
    {H0 : Type} [Group H0] [Finite H0]
    (ξ : R(H0)) (J : Subgroup H0) :
    let XH : Finset (Subgroup H0) := Finset.univ
    let J0 : XH := ⟨J, by simp [XH]⟩
    ((Representation.characterRingRestriction XH) ξ J0 : R(J)) =
      Subgroup.characterRingRestriction J ξ := by
  classical
  dsimp
  -- Both local descriptions are the ordinary restriction of `ξ` from `H0` to `J`.
  apply Subtype.ext
  ext j
  simp [Representation.characterRingRestriction_apply,
    Subgroup.characterRingRestrictionOfLe_apply]

/-- Helper for Remark 11-11.1-3: Frobenius reciprocity rewrites the pairing of an induced linear
character with a class function as the pairing on the subgroup restriction. -/
theorem groupFunctionPairing_induced_linearCharacter_eq_restriction
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
theorem top_local_coordinate_pairing_eq_induced_pairing
    {H0 : Type} [Group H0] [Finite H0]
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
        Subgroup.characterRingRestriction K ξH := by
    -- On the universal subgroup family, the `K`-coordinate is the ordinary restriction to `K`.
    exact top_local_image_restriction_eq_coordinate ξH K
  -- Rewrite the explicit coordinate as a subgroup restriction, then apply Frobenius reciprocity.
  rw [hrestrict]
  simpa [ξH, ξcf] using
    (groupFunctionPairing_induced_linearCharacter_eq_restriction
      (K := K) (α := χ) (x := ξcf)).symm

/-- Helper for Remark 11-11.1-3: on an elementary ambient group, subtracting the index copy of
the trivial character moves an induced linear character into Serre's augmentation subgroup
`R₀'`. -/
theorem induced_linearCharacter_sub_index_smul_one_mem_augmentation_of_isElementary
    {H0 : Type} [Group H0] [Finite H0]
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
subgroup character already belongs to Serre's span `R'`. -/
theorem induced_linearCharacter_mem_elementaryLinearCharacterSpan_of_subgroup_of_isElementary_local
    {H0 : Type} [Group H0] [Finite H0]
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
    -- The augmentation subgroup is the right summand of Serre's span `R'`.
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
theorem local_coordinate_eq_top_local_image_add_zsmul_of_transported_defect
    {H0 : Type} [Group H0] [Finite H0]
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
    have h :
        sH ((Representation.characterRingRestriction XH).toLinearMap ξ) - sH ψ = n • sH δ := by
      rw [← map_sub, ← map_zsmul]
      exact hs_apply
    rwa [hsH ξ] at h
  -- Repackage the subtraction identity into the additive form used by the pairing step.
  exact sub_eq_iff_eq_add'.mp hsplit

/-- Helper for Remark 11-11.1-3: if two ambient characters differ by `n` times an integral
character, then their induced linear-character pairings differ by an explicit `n`-multiple. -/
theorem induced_linearCharacter_pairing_eq_add_n_multiple_of_characterRing_split
    {H0 : Type} [Group H0] [Finite H0]
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
              (((Subgroup.characterRingRestriction K η : R(K)) :
                K → ℂ))⟫ := by
      -- Frobenius reciprocity rewrites the induced pairing as a pairing on the subgroup
      -- restriction of `η`.
      simpa [ηcf, Subgroup.classFunctionRestriction_apply,
        Subgroup.characterRingRestrictionOfLe_apply] using
        (groupFunctionPairing_induced_linearCharacter_eq_restriction
          (K := K) (α := χ) (x := ηcf))
    have hpairK :
        ⟪(χ.toCharacterRing : K → ℂ),
            (((Subgroup.characterRingRestriction K η : R(K)) :
              K → ℂ))⟫ ∈ Set.range (algebraMap ℤ ℂ) :=
      pairing_mem_range_int_of_mem_characterRing_with_linear_character_local
        (η := Subgroup.characterRingRestriction K η) (χ := χ)
    rwa [← hrestrict_pair] at hpairK
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
          have hcoe : ((n • η : R(H0)) : H0 → ℂ) = (n : ℂ) • (η : H0 → ℂ) := by
            ext x
            simp [zsmul_eq_mul]
          rw [hcoe, Representation.groupFunctionPairing_smul_right]
    _ = ⟪Ind[K](χ.toRepresentation.character), (θ : H0 → ℂ)⟫ +
          (n : ℂ) * algebraMap ℤ ℂ m := by
          rw [hm]
    _ = ⟪Ind[K](χ.toRepresentation.character), (θ : H0 → ℂ)⟫ +
          algebraMap ℤ ℂ (n * m) := by
          simp [Int.cast_mul]

/-- Helper for Remark 11-11.1-3: once the transported `J`-coordinate pairing of the ambient
family is divisible by `n` in `ℤ`, the corresponding proper-subgroup pairing against the top local
image is also divisible by `n`. -/
theorem proper_induced_pairing_divisible_of_transport_pairing_int_divisible
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
    -- Apply the residual projector first, then rewrite the resulting identity in image-minus-error
    -- form so the local pairing decomposition lemma can consume it directly.
    have hresidual' : ψH - fH (sH ψH) = (-n) • rH δH := hresidual
    have hneg := congrArg Neg.neg hresidual'
    rw [neg_sub] at hneg
    rw [← neg_smul, neg_neg] at hneg
    exact hneg
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
theorem induced_trivial_pairing_eq_index_trivial_pairing_add_quotient_difference_sum
    {H0 : Type} [Group H0] [Finite H0]
    (M : Subgroup H0) [M.Normal]
    (hcomm : ∀ a b : H0 ⧸ M, a * b = b * a)
    [Fintype ((H0 ⧸ M) →* ℂˣ)]
    (ξ : R(H0)) :
    ⟪(Subgroup.characterRingInduction M (1 : R(M)) : H0 → ℂ), (ξ : H0 → ℂ)⟫ =
      (M.index : ℂ) * ⟪((1 : R(H0)) : H0 → ℂ), (ξ : H0 → ℂ)⟫ +
        ∑ β : (H0 ⧸ M) →* ℂˣ,
          ⟪(((β.comp (QuotientGroup.mk' M)).toCharacterRing - 1 : R(H0)) : H0 → ℂ),
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
  -- Apply the left-linear pairing functional to the quotient-character difference identity.
  have h := congrArg pairLeft
    (induced_trivial_sub_index_smul_one_eq_sum_quotient_linearCharacter_differences
      (H := M) hcomm)
  rw [map_sub, map_zsmul, map_sum] at h
  have hpair_eq :
      pairLeft (Subgroup.characterRingInduction M (1 : R(M))) -
          (M.index : ℂ) * pairLeft (1 : R(H0)) =
        ∑ β : (H0 ⧸ M) →* ℂˣ,
          pairLeft ((β.comp (QuotientGroup.mk' M)).toCharacterRing - 1 : R(H0)) := by
    simpa [zsmul_eq_mul] using h
  -- Move the trivial-line term to the right to recover the source-faithful additive decomposition.
  exact sub_eq_iff_eq_add'.mp hpair_eq

/-- Helper for Remark 11-11.1-3: inducing a linear-character difference from the top subgroup
identifies it with the corresponding ambient linear-character difference. -/
theorem top_induced_difference_eq_ambient_difference
    {H0 : Type} [Group H0] [Finite H0]
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
    have hx : Subgroup.topEquiv.symm (x : H0) = x := Subtype.ext rfl
    simp [β, hx]
  have htop_one :
      Subgroup.characterRingInduction (⊤ : Subgroup H0) (1 : R((⊤ : Subgroup H0))) =
        (1 : R(H0)) := by
    -- Induction from the full subgroup fixes the trivial character.
    have hone : ((1 : H0 →* ℂˣ).toCharacterRing : R(H0)) = 1 := by
      apply Subtype.ext
      ext h
      simp [MonoidHom.toCharacterRing_apply]
    simpa [MonoidHom.one_comp, Subgroup.toCharacterRing_one, hone] using
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
theorem ambient_difference_pairing_eq_top_induced_difference_pairing
    {H0 : Type} [Group H0] [Finite H0]
    (ξ : R(H0)) (α : (⊤ : Subgroup H0) →* ℂˣ) :
    ⟪(((α.comp Subgroup.topEquiv.symm.toMonoidHom).toCharacterRing - 1 : R(H0)) :
          H0 → ℂ),
        (ξ : H0 → ℂ)⟫ =
      ⟪((Subgroup.characterRingInduction (⊤ : Subgroup H0)
            (α.toCharacterRing - 1) : R(H0)) : H0 → ℂ),
          (ξ : H0 → ℂ)⟫ := by
  -- Rewrite the top-induced difference to the canonical ambient difference term.
  rw [top_induced_difference_eq_ambient_difference (H0 := H0) α]

/-- Helper for Remark 11-11.1-3: inducing a linear-character difference from the top subgroup
recovers the corresponding ambient linear-character difference, so the `E = ⊤` generators already
lie in Serre's augmentation subgroup. -/
theorem top_induced_linearCharacter_difference_mem_augmentation_of_isElementary
    {H0 : Type} [Group H0] [Finite H0]
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
theorem top_linearCharacter_eq_one_of_bot_eq_top_local
    {H0 : Type} [Group H0]
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
theorem top_induced_difference_eq_zero_of_bot_eq_top_local
    {H0 : Type} [Group H0] [Finite H0]
    (htrivial : (⊥ : Subgroup H0) = ⊤)
    (α : (⊤ : Subgroup H0) →* ℂˣ) :
    Subgroup.characterRingInduction (⊤ : Subgroup H0) (α.toCharacterRing - 1) = 0 := by
  -- After collapsing the unique top character to `1`, the induced difference is literally zero.
  rw [top_linearCharacter_eq_one_of_bot_eq_top_local htrivial α]
  simp [Subgroup.toCharacterRing_one]

/-- Helper for Remark 11-11.1-3: transporting a nontrivial top-subgroup character to the ambient
group still has proper kernel. -/
theorem kernel_of_nontrivial_top_character_lt_top_local
    {H0 : Type} [Group H0]
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
    rw [show (α.comp Subgroup.topEquiv.symm.toMonoidHom).ker = ⊤ from hker]
    simp
  -- Reading kernel membership back through `⊤ ≃ H0` shows the original top character is trivial.
  simpa [MonoidHom.mem_ker] using hxker

/-- Helper for Remark 11-11.1-3: when `H` is trivial, the transported family indexed by all
subgroups of `H` is just the ordinary restriction family of the ambient coordinate `x H`. -/
theorem singleton_transported_family_eq_ambient_restriction
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
    simp [← MonoidHom.range_eq_map, Subgroup.subtype_range]
  -- With only the top subgroup left, the transported coordinate is literally the ambient one.
  simp only [Representation.characterRingRestriction_apply,
    Subgroup.characterRingTransport_apply,
    Subgroup.characterRingRestrictionOfLe_apply]
  have key : ∀ (A : X) (_ : A = H) (y : A.1) (_ : (y : G) = ((j : H.1) : G)),
      ((x A : R(A.1)) : A.1 → ℂ) y = ((x H : R(H.1)) : H.1 → ℂ) (j : H.1) := by
    intro A hA y hy
    subst hA
    exact congrArg _ (Subtype.ext hy)
  exact key _ htopX _ (by simp [Subgroup.coe_equivMapOfInjective_apply])

/-- Helper for Remark 11-11.1-3: in the trivial-ambient branch, gluing the singleton family back
with `sH` recovers the original ambient coordinate `x H`. -/
theorem singleton_top_local_image_eq_ambient_coordinate
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



end CharacterizationOfCharacters

end Representation
