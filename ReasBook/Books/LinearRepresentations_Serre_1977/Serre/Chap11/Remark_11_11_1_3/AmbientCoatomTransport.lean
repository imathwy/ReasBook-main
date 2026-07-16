import Mathlib
import LinearRepresentations_Serre_1977.Serre.Chap10.Definition_10_10_1_3
import LinearRepresentations_Serre_1977.Serre.Chap11.Remark_11_11_1_3.TensorCharacterRingRestriction
import LinearRepresentations_Serre_1977.Serre.Chap11.Remark_11_11_1_3.RestrictionFamily
import LinearRepresentations_Serre_1977.Serre.Chap11.Remark_11_11_1_3.ElementaryConjugation
import LinearRepresentations_Serre_1977.Serre.Chap11.Remark_11_11_1_3.ElementaryDetection
import LinearRepresentations_Serre_1977.Serre.Chap11.Remark_11_11_1_3.IntegralRestrictionSplitting
import LinearRepresentations_Serre_1977.Serre.Chap11.Remark_11_11_1_3.ElementaryCoherence
import LinearRepresentations_Serre_1977.Serre.Chap11.Remark_11_11_1_3.SubgroupLinearPairing

/-!
Support file for Remark 11-11.1-3: dependent-identity transport helpers used by the ambient
coatom induction. All lemmas here are small congruence/reindexing devices that move pairing
statements across propositional subgroup identities without ever rewriting inside dependent
types: the equality is consumed by `subst` over an opaque variable, or by an explicit
`MulEquiv` reindexing of the underlying finite sums.
-/

noncomputable section

universe u v

namespace Representation

section CharacterizationOfCharacters

open scoped Pointwise Representation SubgroupInduction TensorProduct

variable {G : Type} [Group G] [Finite G]

/-- Helper for Remark 11-11.1-3: every subgroup of a finite group is finite. -/
local instance fintypeHelperLocalAmbientCoatomTransport1 (H : Subgroup G) : Fintype H :=
  Fintype.ofFinite H

/-- Helper for Remark 11-11.1-3: the normalized pairing is invariant under reindexing both
function arguments along a group isomorphism. -/
theorem groupFunctionPairing_reindex_mulEquiv_local
    {A B : Type} [Group A] [Finite A] [Group B] [Finite B]
    (e : A ≃* B) (f g : A → ℂ) (f' g' : B → ℂ)
    (hf : ∀ a : A, f a = f' (e a)) (hg : ∀ a : A, g a = g' (e a)) :
    ⟪f, g⟫ = ⟪f', g'⟫ := by
  classical
  letI : Fintype A := Fintype.ofFinite A
  letI : Fintype B := Fintype.ofFinite B
  rw [Representation.groupFunctionPairing_eq_card_inv_sum_apply_mul_inv_apply,
    Representation.groupFunctionPairing_eq_card_inv_sum_apply_mul_inv_apply]
  have hcard : (Nat.card A : ℂ) = (Nat.card B : ℂ) := by
    exact_mod_cast congrArg Nat.cast (Nat.card_congr e.toEquiv)
  rw [hcard]
  refine congrArg (fun z : ℂ ↦ (Nat.card B : ℂ)⁻¹ * z) ?_
  refine Fintype.sum_equiv e.toEquiv _ _ fun a ↦ ?_
  -- Reindex each summand along the isomorphism; inversion commutes with the isomorphism.
  rw [hf a, hg a⁻¹]
  simp

/-- Helper for Remark 11-11.1-3: coordinates of an `X`-indexed character family agree pointwise
on equal index subgroups. The index equality is consumed by `subst`, so no dependent rewriting
is ever attempted at the call sites. -/
theorem subgroup_family_coordinate_apply_congr_local
    (X : Finset (Subgroup G)) (x : (H : X) → R(H.1))
    {p q : X} (hpq : p = q) (g : G) (hp : g ∈ p.1) (hq : g ∈ q.1) :
    ((x p : R(p.1)) : p.1 → ℂ) ⟨g, hp⟩ = ((x q : R(q.1)) : q.1 → ℂ) ⟨g, hq⟩ := by
  subst hpq
  rfl

/-- Helper for Remark 11-11.1-3: the transported linear character evaluates through any chosen
preimage of the underlying ambient element. -/
theorem mapped_linear_character_local_apply_eq
    (H : Subgroup G) (K : Subgroup H) (χ : K →* ℂˣ)
    (y : K.map H.subtype) (k : K) (hk : ((k : H) : G) = (y : G)) :
    mapped_linear_character_local H K χ y = χ k := by
  have he : (K.equivMapOfInjective H.subtype H.subtype_injective) k = y := by
    apply Subtype.ext
    simpa [Subgroup.coe_equivMapOfInjective_apply] using hk
  show χ ((K.equivMapOfInjective H.subtype H.subtype_injective).symm y) = χ k
  rw [← he, MulEquiv.symm_apply_apply]

/-- Helper for Remark 11-11.1-3: pairings over propositionally equal subgroups agree as soon as
both function arguments agree on the underlying ambient elements. -/
theorem subgroup_pairing_eq_of_subgroup_eq_local
    {S S' : Subgroup G} (h : S = S')
    (f : S → ℂ) (f' : S' → ℂ)
    (hf : ∀ (g : G) (hg : g ∈ S) (hg' : g ∈ S'), f ⟨g, hg⟩ = f' ⟨g, hg'⟩)
    (k : S → ℂ) (k' : S' → ℂ)
    (hk : ∀ (g : G) (hg : g ∈ S) (hg' : g ∈ S'), k ⟨g, hg⟩ = k' ⟨g, hg'⟩) :
    ⟪f, k⟫ = ⟪f', k'⟫ := by
  subst h
  have hf' : f = f' := funext fun s ↦ hf s.1 s.2 s.2
  have hk' : k = k' := funext fun s ↦ hk s.1 s.2 s.2
  rw [hf', hk']

/-- Helper for Remark 11-11.1-3: mapping the top subgroup back along the subtype recovers the
subgroup itself. -/
theorem subgroup_top_map_subtype_eq_local (M : Subgroup G) :
    (⊤ : Subgroup M).map M.subtype = M := by
  ext g
  constructor
  · rintro ⟨y, -, rfl⟩
    exact y.2
  · intro hg
    exact ⟨⟨g, hg⟩, Subgroup.mem_top _, rfl⟩

/-- Helper for Remark 11-11.1-3: pushing a subgroup of `M` to the mapped copy `M.map H.subtype`
and then into the ambient group is the same as climbing the chain `L ≤ M ≤ H` directly. -/
theorem subgroup_chain_map_equiv_map_eq_local
    (H : Subgroup G) (M : Subgroup H) (L : Subgroup M) :
    (L.map (M.equivMapOfInjective H.subtype H.subtype_injective).toMonoidHom).map
        (M.map H.subtype).subtype =
      (L.map M.subtype).map H.subtype := by
  have hcomp :
      ((M.map H.subtype).subtype).comp
          (M.equivMapOfInjective H.subtype H.subtype_injective).toMonoidHom =
        H.subtype.comp M.subtype := by
    ext m
    simp [Subgroup.coe_equivMapOfInjective_apply]
  rw [Subgroup.map_map, Subgroup.map_map, hcomp]

/-- Algebra helper for `residual_coordinate_pairing_decomposition_shared`: rearrange the
residual-projector identity into the image-minus-family form. -/
private theorem image_residual_of_residual_projector_shared
    {M N : Type*} [AddCommGroup M] [Module ℤ M] [AddCommGroup N] [Module ℤ N]
    (fH : M →ₗ[ℤ] N) (sH : N →ₗ[ℤ] M) (ψ δ : N) {n : ℤ}
    (h : ((LinearMap.id : N →ₗ[ℤ] N) - fH.comp sH) ψ =
      (-n) • (((LinearMap.id : N →ₗ[ℤ] N) - fH.comp sH) δ)) :
    fH (sH ψ) - ψ = n • (((LinearMap.id : N →ₗ[ℤ] N) - fH.comp sH) δ) := by
  have h' : ψ - fH (sH ψ) = (-n) • (((LinearMap.id : N →ₗ[ℤ] N) - fH.comp sH) δ) := by
    simpa [LinearMap.sub_apply, LinearMap.comp_apply] using h
  have hneg := congrArg Neg.neg h'
  simpa [neg_sub, neg_smul, neg_neg] using hneg

/-- Helper for Remark 11-11.1-3: the transported local family pairing decomposes into the
local-image pairing plus an explicit `n`-multiple. This is the shared (de-privatized) form of the
residual-coordinate decomposition needed both by the ambient coatom induction and by the residual
family analysis. -/
theorem residual_coordinate_pairing_decomposition_shared
    (X : Finset (Subgroup G))
    (hXelem : ∀ H : Subgroup G, H ∈ X ↔ IsElementary H)
    {x : (H : X) → R(H.1)} {t : elementary_coherence_target X hXelem} {n : ℤ}
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
    ∃ m : ℤ,
      ⟪(χ.toCharacterRing : K → ℂ), (ψH K0 : K → ℂ)⟫ =
        ⟪(χ.toCharacterRing : K → ℂ),
            (((Representation.characterRingRestriction XH) (sH ψH) K0 : R(K)) : K → ℂ)⟫ +
          algebraMap ℤ ℂ (n * m) := by
  classical
  intro XH ψH K0
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
  have himage_residual : fH (sH ψH) - ψH = n • rH δH :=
    image_residual_of_residual_projector_shared fH sH ψH δH hresidual
  exact
    local_residual_pairing_decomposition_of_defect_multiple XH sH hsH himage_residual K0 χ

end CharacterizationOfCharacters

end Representation
