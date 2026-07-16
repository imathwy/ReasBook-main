import Mathlib
import LinearRepresentations_Serre_1977.Serre.Chap10.Definition_10_10_1_3
import LinearRepresentations_Serre_1977.Serre.Chap11.Remark_11_11_1_3.TensorCharacterRingRestriction
import LinearRepresentations_Serre_1977.Serre.Chap11.Remark_11_11_1_3.RestrictionFamily
import LinearRepresentations_Serre_1977.Serre.Chap11.Remark_11_11_1_3.ElementaryConjugation
import LinearRepresentations_Serre_1977.Serre.Chap11.Remark_11_11_1_3.ElementaryDetection
import LinearRepresentations_Serre_1977.Serre.Chap11.Remark_11_11_1_3.IntegralRestrictionSplitting
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

noncomputable section

universe v

namespace Representation

section CharacterizationOfCharacters

open scoped Pointwise Representation SubgroupInduction TensorProduct

variable {G : Type} [Group G] [Finite G]
variable {A : Type v} [CommRing A]

local notation:max s " •ᶜ " H => (MulAut.conj s • H : Subgroup G)

/-- Helper for Remark 11-11.1-3: every subgroup of a finite group is finite. -/
local instance fintypeHelperLocalResidualIntegralityCriterion1 (H : Subgroup G) : Fintype H := Fintype.ofFinite H

/-- Helper for Remark 11-11.1-3: pairing the `K.map H.subtype` coordinate of a global restriction
family against the transported linear character agrees with the ambient induced pairing. -/
theorem mapped_linear_character_pairing_eq_induced_global_pairing
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

/-- Pairing against a fixed left function, as a `ℤ`-linear functional on the character ring. -/
private noncomputable def leftPairingLinear_local {H0 : Type} [Group H0] [Finite H0]
    (f : H0 → ℂ) : R(H0) →ₗ[ℤ] ℂ :=
  { toFun := fun η ↦ ⟪f, (η : H0 → ℂ)⟫
    map_add' := by
      intro η θ
      simpa using Representation.groupFunctionPairing_add_right f (η : H0 → ℂ) (θ : H0 → ℂ)
    map_smul' := by
      intro n η
      have hcoe : ((n • η : R(H0)) : H0 → ℂ) = (n : ℂ) • (η : H0 → ℂ) := by
        ext x
        simp [zsmul_eq_mul]
      have h := Representation.groupFunctionPairing_smul_right
        (a := (n : ℂ)) (φ := f) (ψ := (η : H0 → ℂ))
      simp only [RingHom.id_apply]
      rw [hcoe, h, zsmul_eq_mul] }

/-- Helper for Remark 11-11.1-3: after removing the global contribution chosen by `s`, the local
pairing against a transported linear character factors through the range of the coherence defect.
-/
theorem residual_linear_character_pairing_factors_through_coherence_defect
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
  intro KX
  obtain ⟨q, hq⟩ :=
    characterRingRestriction_residual_factors_through_coherence_defect X hXelem s hs
  let pairingLinear : R(KX.1) →ₗ[ℤ] ℂ :=
    leftPairingLinear_local
      (((mapped_linear_character_local H.1 K χ).toCharacterRing : R(KX.1)) : KX.1 → ℂ)
  let coordPair : ((J : X) → R(J.1)) →ₗ[ℤ] ℂ :=
    pairingLinear.comp (LinearMap.proj (R := ℤ) (φ := fun J : X ↦ R(J.1)) KX)
  refine ⟨coordPair.comp q, fun ψ ↦ ?_⟩
  have hqψ := LinearMap.congr_fun hq ψ
  simp only [LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.id_apply] at hqψ
  have hglobal :
      coordPair ((Representation.characterRingRestriction X).toLinearMap (s ψ)) =
        ⟪Ind[KX.1](((mapped_linear_character_local H.1 K χ).toRepresentation.character)),
            (s ψ : G → ℂ)⟫ := by
    -- The `KX`-coordinate of a genuine global restriction family is measured by ambient induction.
    simpa [coordPair, pairingLinear, leftPairingLinear_local] using
      mapped_linear_character_pairing_eq_induced_global_pairing
        X hXelem H K χ (s ψ)
  have hcoord :
      coordPair ψ =
        ⟪((mapped_linear_character_local H.1 K χ).toCharacterRing : KX.1 → ℂ),
            (ψ KX : KX.1 → ℂ)⟫ := rfl
  rw [LinearMap.comp_apply, hqψ, map_sub coordPair, hglobal, hcoord]

/-- Helper for Remark 11-11.1-3: on an elementary finite group, integrality of all linear
pairings on subgroups extends by linearity to every monomial character. -/
theorem pairing_mem_range_of_mem_monomialCharacterSpan_on_elementary_group
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
      have hcoe : ((ξ + ζ : R(H)) : H → ℂ) = (ξ : H → ℂ) + (ζ : H → ℂ) := rfl
      rw [hcoe, Representation.groupFunctionPairing_add_left, ← ha, ← hb,
        ← map_add (algebraMap ℤ ℂ) a b]
  | smul n ξ _ hξ =>
      rcases hξ with ⟨a, ha⟩
      refine ⟨n * a, ?_⟩
      have hcoe : ((n • ξ : R(H)) : H → ℂ) = (n : ℂ) • (ξ : H → ℂ) := by
        ext x
        simp [zsmul_eq_mul]
      rw [hcoe, Representation.groupFunctionPairing_smul_left, ← ha,
        map_mul (algebraMap ℤ ℂ) n a]
      simp [eq_intCast]

/-- Helper for Remark 11-11.1-3: on an elementary finite group, a class function is integral as
soon as all of its linear pairings on elementary subgroups are integers. -/
theorem integer_pairing_criterion_for_characterRing_on_elementary_subgroups
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
    refine sum_mem ?_
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
          simpa [fdRepCharacterRing, Representation.groupFunctionPairing_comm] using ha.symm
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
    exact (R(H)).smul_mem hb a
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
theorem scaled_residual_coordinate_mem_characterRing
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
    exact sub_eq_iff_eq_add'.mp hp_defect
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
          have hcoe : ((n • t.1 p : R(KX.1)) : KX.1 → ℂ) =
              (n : ℂ) • (t.1 p : KX.1 → ℂ) := by
            ext y
            simp [zsmul_eq_mul]
          rw [hcoe, Representation.groupFunctionPairing_smul_right]
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



end CharacterizationOfCharacters

end Representation
