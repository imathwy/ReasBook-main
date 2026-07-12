import Mathlib
import LinearRepresentations_Serre_1977.Chap10.Definition_10_10_1_3
import LinearRepresentations_Serre_1977.Chap11.Remark_11_11_1_3.TensorCharacterRingRestriction
import LinearRepresentations_Serre_1977.Chap11.Remark_11_11_1_3.RestrictionFamily
import LinearRepresentations_Serre_1977.Chap11.Remark_11_11_1_3.ElementaryConjugation
import LinearRepresentations_Serre_1977.Chap11.Remark_11_11_1_3.ElementaryDetection
import LinearRepresentations_Serre_1977.Chap11.Remark_11_11_1_3.IntegralRestrictionSplitting
import LinearRepresentations_Serre_1977.Chap11.Remark_11_11_1_3.ElementaryCoherence
import LinearRepresentations_Serre_1977.Chap11.Remark_11_11_1_3.SubgroupLinearPairing
import LinearRepresentations_Serre_1977.Chap11.Remark_11_11_1_3.TopLocalPairing
import LinearRepresentations_Serre_1977.Chap11.Remark_11_11_1_3.CoatomDivisibility
import LinearRepresentations_Serre_1977.Chap11.Remark_11_11_1_3.KernelQuotientCharacters
import LinearRepresentations_Serre_1977.Chap11.Remark_11_11_1_3.CyclicQuotientPairings
import LinearRepresentations_Serre_1977.Chap11.Remark_11_11_1_3.QuotientPullbackPairings

noncomputable section

universe v

namespace Representation

section CharacterizationOfCharacters

open scoped Pointwise Representation SubgroupInduction TensorProduct

variable {G : Type} [Group G] [Finite G]
variable {A : Type v} [CommRing A]

local notation:max s " •ᶜ " H => (MulAut.conj s • H : Subgroup G)

/-- Helper for Remark 11-11.1-3: every subgroup of a finite group is finite. -/
local instance fintypeHelperLocalQuotientPullbackDivisibility1 (H : Subgroup G) : Fintype H := Fintype.ofFinite H

/-- Helper for Remark 11-11.1-3: the degree-one characters of a finite group form a finite type. -/
noncomputable local instance fintypeHelperLocalQuotientPullbackDivisibility2
    (Q : Type*) [Group Q] [Finite Q] : Fintype (Q →* ℂˣ) := Fintype.ofFinite _

/-- Helper for Remark 11-11.1-3: quotients of finite groups are finite types. -/
noncomputable local instance fintypeHelperLocalQuotientPullbackDivisibility3
    (Q : Type*) [Group Q] [Finite Q] (M : Subgroup Q) [M.Normal] : Fintype (Q ⧸ M) :=
  Fintype.ofFinite _

/-- Helper for Remark 11-11.1-3: one canonical classical decidable equality for characters. -/
noncomputable local instance (priority := 2000) fintypeHelperLocalQuotientPullbackDivisibility4
    (Q : Type*) [Group Q] : DecidableEq (Q →* ℂˣ) := Classical.decEq _

attribute [local instance] Classical.propDecidable
/-- Helper for Remark 11-11.1-3: once the faithful quotient block is known to lie in the
`ℤ`-span of proper quotient induced-trivial characters, applying the quotient pullback pairing
transports that span directly to the ambient overgroup pairing span. -/
theorem quotient_pullback_pairing_mem_span_overgroups_of_mem_span_induced_trivial
    {H0 : Type} [Group H0] [Finite H0]
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
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hη
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
  · intro η₁ η₂ _ _ hη₁ hη₂
    -- Additivity of the pairing linear map preserves target-span membership.
    simpa using
      (Submodule.add_mem
        (Submodule.span ℤ
          (Set.range fun J : {J : Subgroup H0 // β.ker ≤ J ∧ J < ⊤} ↦
            ⟪(Subgroup.characterRingInduction J.1 (1 : R(J.1)) : H0 → ℂ), (ξ : H0 → ℂ)⟫))
        hη₁ hη₂)
  · intro m η' _ hη'
    -- The target span is a `ℤ`-submodule, so integer scalar multiples stay inside it.
    have hmap : quotient_pullback_pairing_linearMap β ξ (m • η') =
        m • quotient_pullback_pairing_linearMap β ξ η' := map_zsmul _ m η'
    rw [hmap]
    exact Submodule.smul_mem _ m hη'

/-- Helper for Remark 11-11.1-3: once a scalar pairing lies in the `ℤ`-span of the proper
overgroup induced-trivial pairings above `β.ker`, the local proper-branch theorem packages the
whole span witness into a single `n`-multiple. -/
theorem overgroup_pairing_span_divisible_of_local_proper_branch
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
  let XH : Finset (Subgroup H.1) := Finset.univ
  let ψH : (J : XH) → R(J.1) := fun J ↦
    Subgroup.characterRingTransport
      (J.1.equivMapOfInjective H.1.subtype H.1.subtype_injective)
      (x ⟨J.1.map H.1.subtype,
        (hXelem (J.1.map H.1.subtype)).2 <|
          isElementary_of_mulEquiv_local
            (J.1.equivMapOfInjective H.1.subtype H.1.subtype_injective)
            (subgroup_isElementary_of_isElementary_local J.1 ((hXelem H.1).1 H.2))⟩)
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
theorem quotient_pullback_pairing_divisible_of_quotient_induced_trivial_span
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
theorem faithful_cyclic_layer_pairing_divisible_of_quotient_induced_trivial_span
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
          ∑ γ ∈ ((Finset.univ.erase βq).filter fun γ => γ.ker = ⊥),
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
        ∑ γ ∈
            ((Finset.univ.erase
                (QuotientGroup.lift β.ker β (show β.ker ≤ β.ker from le_rfl))).filter
              fun γ => γ.ker = ⊥),
            ⟪(((γ.comp (QuotientGroup.mk' β.ker)).toCharacterRing - 1 : R(H.1)) :
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
      ∑ γ ∈ ((Finset.univ.erase βq).filter fun γ => γ.ker = ⊥),
        ((γ.toCharacterRing - 1 : R(H.1 ⧸ β.ker)))
  obtain ⟨bC, hbC⟩ :=
    quotient_pullback_pairing_divisible_of_quotient_induced_trivial_span
      X hXelem hdx H sH hsH hproper (β := β) (η := η) hη
  refine ⟨bC, ?_⟩
  -- Rewrite the faithful cyclic layer as the pullback pairing of the quotient-side faithful block
  -- and then apply the packaged quotient-span witness.
  calc
    (β.ker.index : ℂ) * ⟪((1 : R(H.1)) : H.1 → ℂ), (ξH : H.1 → ℂ)⟫ +
        ∑ γ ∈ ((Finset.univ.erase βq).filter fun γ => γ.ker = ⊥),
          ⟪(((γ.comp (QuotientGroup.mk' β.ker)).toCharacterRing - 1 : R(H.1)) :
                H.1 → ℂ),
              (ξH : H.1 → ℂ)⟫ =
      quotient_pullback_pairing_linearMap β ξH η := by
        simpa [βq, η, ξH] using
          faithful_quotient_top_layer_eq_quotient_pullback_pairing
            (β := β)
            (ξ := ξH)
    _ = algebraMap ℤ ℂ (n * bC) := hbC


end CharacterizationOfCharacters

end Representation
