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
import LinearRepresentations_Serre_1977.Chap11.Remark_11_11_1_3.QuotientPullbackDivisibility
import LinearRepresentations_Serre_1977.Chap11.Remark_11_11_1_3.StrictBranchResidual
import LinearRepresentations_Serre_1977.Chap11.Remark_11_11_1_3.MappedCoatomSlices
import LinearRepresentations_Serre_1977.Chap11.Remark_11_11_1_3.MappedCoatomReindexing
import LinearRepresentations_Serre_1977.Chap11.Remark_11_11_1_3.StrictKernelGrowth
import LinearRepresentations_Serre_1977.Chap11.Remark_11_11_1_3.ChosenCoatomFaithful

noncomputable section

universe v

namespace Representation

section CharacterizationOfCharacters

open scoped Pointwise Representation SubgroupInduction TensorProduct

variable {G : Type} [Group G] [Finite G]
variable {A : Type v} [CommRing A]

local notation:max s " •ᶜ " H => (MulAut.conj s • H : Subgroup G)

/-- Helper for Remark 11-11.1-3: every subgroup of a finite group is finite. -/
local instance fintypeHelperLocalKernelQuotientRecursion1 (H : Subgroup G) : Fintype H := Fintype.ofFinite H

/-- Helper for Remark 11-11.1-3: the degree-one characters of a finite group form a finite type. -/
noncomputable local instance fintypeHelperLocalKernelQuotientRecursionA
    (Q : Type*) [Group Q] [Finite Q] : Fintype (Q →* ℂˣ) := Fintype.ofFinite _

/-- Helper for Remark 11-11.1-3: quotients of finite groups are finite types. -/
noncomputable local instance fintypeHelperLocalKernelQuotientRecursionB
    (Q : Type*) [Group Q] [Finite Q] (M : Subgroup Q) : Fintype (Q ⧸ M) :=
  Fintype.ofFinite _

/-- Helper for Remark 11-11.1-3: one canonical classical decidable equality for characters. -/
noncomputable local instance (priority := 2000) fintypeHelperLocalKernelQuotientRecursionC
    (Q : Type*) [Group Q] : DecidableEq (Q →* ℂˣ) := Classical.decEq _

attribute [local instance] Classical.propDecidable

/-- Helper for Remark 11-11.1-3: the cyclic quotient owner theorem should package the kernel-index
trivial line together with the faithful erased quotient-character summands directly from the proper
quotient-subgroup branch, without passing through the false raw span statement. -/
theorem cyclic_quotient_top_layer_pairing_divisible_of_local_proper_branch
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
      ⟪(((γ.comp (QuotientGroup.mk' β.ker)).toCharacterRing - 1 : R(H.1)) :
            H.1 → ℂ),
          ((sH ψH : R(H.1)) : H.1 → ℂ)⟫
    ∃ bC : ℤ,
      (β.ker.index : ℂ) * ⟪((1 : R(H.1)) : H.1 → ℂ), ((sH ψH : R(H.1)) : H.1 → ℂ)⟫ +
        ∑ γ ∈ ((Finset.univ.erase βq).filter fun γ => γ.ker = ⊥), term γ =
          algebraMap ℤ ℂ (n * bC) := by
  -- Route correction: the quotient-side span owner is false. The main theorem is now just the
  -- interface wrapper around the kernel-index induction owner for the faithful cyclic layer.
  simpa using
    cyclic_faithful_layer_pairing_divisible_by_kernel_index_induction
      X hXelem hdx H sH hsH hproper β hβ

/-- Helper for Remark 11-11.1-3: the cyclic quotient's top layer must be packaged as one block.
This is the source-faithful replacement for the failed attempt to prove the scaled trivial line and
the faithful erased quotient-character sum separately. -/
theorem kernel_scaled_trivial_plus_faithful_erased_sum_divisible
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
      ⟪(((γ.comp (QuotientGroup.mk' β.ker)).toCharacterRing - 1 : R(H.1)) :
            H.1 → ℂ),
          ((sH ψH : R(H.1)) : H.1 → ℂ)⟫
    ∃ bC : ℤ,
      (β.ker.index : ℂ) * ⟪((1 : R(H.1)) : H.1 → ℂ), ((sH ψH : R(H.1)) : H.1 → ℂ)⟫ +
        ∑ γ ∈ ((Finset.univ.erase βq).filter fun γ => γ.ker = ⊥), term γ =
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
theorem ambient_difference_pairing_divisible_kernel_growth_step
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
          ⟪(((δ.toCharacterRing - 1 : R(H.1)) : H.1 → ℂ)),
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
      ⟪(((β.toCharacterRing - 1 : R(H.1)) : H.1 → ℂ)),
          ((sH ψH : R(H.1)) : H.1 → ℂ)⟫ =
        algebraMap ℤ ℂ (n * b) := by
  classical
  dsimp at ih ⊢
  let βq : (H.1 ⧸ β.ker) →* ℂˣ :=
    QuotientGroup.lift β.ker β (show β.ker ≤ β.ker from le_rfl)
  let term : ((H.1 ⧸ β.ker) →* ℂˣ) → ℂ := fun γ ↦
    ⟪(((γ.comp (QuotientGroup.mk' β.ker)).toCharacterRing - 1 : R(H.1)) :
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
      X hXelem (t := t) (n := n) H sH β ih
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
      ∑ γ ∈ Finset.univ.erase βq, term γ =
        ∑ γ ∈ ((Finset.univ.erase βq).filter fun γ => γ.ker = ⊥), term γ +
          ∑ γ ∈ ((Finset.univ.erase βq).filter fun γ => γ.ker ≠ ⊥), term γ := by
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
      ⟪(((β.toCharacterRing - 1 : R(H.1)) : H.1 → ℂ)),
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
            ∑ γ ∈ ((Finset.univ.erase βq).filter fun γ => γ.ker = ⊥), term γ)) -
          ∑ γ ∈ ((Finset.univ.erase βq).filter fun γ => γ.ker ≠ ⊥), term γ := by
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
                      ((hXelem H.1).1 H.2))⟩)))
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
            ∑ γ ∈ ((Finset.univ.erase βq).filter fun γ => γ.ker = ⊥), term γ) +
            ⟪(((β.toCharacterRing - 1 : R(H.1)) : H.1 → ℂ)),
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
            ∑ γ ∈ ((Finset.univ.erase βq).filter fun γ => γ.ker ≠ ⊥), term γ := by
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
              ⟪(((β.toCharacterRing - 1 : R(H.1)) : H.1 → ℂ)),
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
                ∑ γ ∈ Finset.univ.erase βq, term γ := by
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
              ⟪(((β.toCharacterRing - 1 : R(H.1)) : H.1 → ℂ)),
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
                (∑ γ ∈ ((Finset.univ.erase βq).filter fun γ => γ.ker = ⊥), term γ +
                  ∑ γ ∈ ((Finset.univ.erase βq).filter fun γ => γ.ker ≠ ⊥), term γ) := by
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
              ∑ γ ∈ ((Finset.univ.erase βq).filter fun γ => γ.ker = ⊥), term γ) +
              ⟪(((β.toCharacterRing - 1 : R(H.1)) : H.1 → ℂ)),
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
              ∑ γ ∈ ((Finset.univ.erase βq).filter fun γ => γ.ker ≠ ⊥), term γ := by
              ring
    have htarget_plus :
        (⟪(((β.toCharacterRing - 1 : R(H.1)) : H.1 → ℂ)),
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
          ∑ γ ∈ ((Finset.univ.erase βq).filter fun γ => γ.ker ≠ ⊥), term γ) =
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
            ∑ γ ∈ ((Finset.univ.erase βq).filter fun γ => γ.ker = ⊥), term γ) := by
      linear_combination -hdecomp_split
    linear_combination htarget_plus
  -- Subtract the two packaged `n`-multiples from the induced-kernel witness to isolate the
  -- distinguished ambient difference term.
  calc
    ⟪(((β.toCharacterRing - 1 : R(H.1)) : H.1 → ℂ)),
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
            ∑ γ ∈ ((Finset.univ.erase βq).filter fun γ => γ.ker = ⊥), term γ)) -
          ∑ γ ∈ ((Finset.univ.erase βq).filter fun γ => γ.ker ≠ ⊥), term γ := htarget
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
theorem ambient_difference_pairing_divisible_of_nontrivial_character_by_kernel_growth
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
      ⟪(((β.toCharacterRing - 1 : R(H.1)) : H.1 → ℂ)),
          ((sH ψH : R(H.1)) : H.1 → ℂ)⟫ =
        algebraMap ℤ ℂ (n * b) := by
  classical
  dsimp
  let P : ℕ → Prop := fun m =>
    ∀ δ : H.1 →* ℂˣ, δ ≠ 1 → δ.ker.index = m →
      ∃ b : ℤ,
        ⟪(((δ.toCharacterRing - 1 : R(H.1)) : H.1 → ℂ)),
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
theorem erased_quotient_character_difference_divisible
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
      ⟪(((γ.comp (QuotientGroup.mk' β.ker)).toCharacterRing - 1 : R(H.1)) :
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
        X hXelem (t := t) (n := n) H sH β γ hδ
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
theorem kernel_quotient_remainder_sum_divisible
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
    ∃ bSum : ℤ,
      ∑ γ ∈ Finset.univ.erase βq,
        ⟪(((γ.comp (QuotientGroup.mk' β.ker)).toCharacterRing - 1 : R(H.1)) :
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
        algebraMap ℤ ℂ (n * bSum) := by
  classical
  dsimp
  let βq : (H.1 ⧸ β.ker) →* ℂˣ :=
    QuotientGroup.lift β.ker β (show β.ker ≤ β.ker from le_rfl)
  let term : ((H.1 ⧸ β.ker) →* ℂˣ) → ℂ := fun γ ↦
    ⟪(((γ.comp (QuotientGroup.mk' β.ker)).toCharacterRing - 1 : R(H.1)) :
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
    obtain ⟨bSum, hbSum⟩ :=
      finset_sum_int_multiples (s := Finset.univ.erase βq) (f := term) (n := n) hterm
    refine ⟨bSum, ?_⟩
    simpa [term] using hbSum
  intro γ hγ
  -- The whole-sum statement is now only a packaging wrapper around the single-character witness.
  simpa [term, βq] using
    erased_quotient_character_difference_divisible
      X hXelem hdx H sH hsH hproper β γ hγ

/-- Helper for Remark 11-11.1-3: the nontrivial top-character branch should recurse on the proper
kernel of the transported ambient character, not on a false coatom identification of that kernel.
-/
theorem top_difference_pairing_divisible_of_nontrivial_top_character_via_kernel_quotient_recursion
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
  let ψH : (J : (Finset.univ : Finset (Subgroup H.1))) → R(J.1) := fun J ↦
    Subgroup.characterRingTransport
      (J.1.equivMapOfInjective H.1.subtype H.1.subtype_injective)
      (x ⟨J.1.map H.1.subtype,
        (hXelem (J.1.map H.1.subtype)).2 <|
          isElementary_of_mulEquiv_local
            (J.1.equivMapOfInjective H.1.subtype H.1.subtype_injective)
            (subgroup_isElementary_of_isElementary_local J.1 ((hXelem H.1).1 H.2))⟩)
  let β : H.1 →* ℂˣ := α.comp Subgroup.topEquiv.symm.toMonoidHom
  have hβ : β ≠ 1 := by
    intro hβone
    apply hα
    refine MonoidHom.ext fun x ↦ ?_
    -- Evaluate the ambient equality back on the top subgroup through `⊤ ≃ H`.
    simpa [β] using DFunLike.congr_fun hβone x.1
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
      ⟪(((β.toCharacterRing - 1 : R(H.1)) : H.1 → ℂ)),
          ((sH ψH : R(H.1)) : H.1 → ℂ)⟫ := by
            exact
              (ambient_difference_pairing_eq_top_induced_difference_pairing
                (ξ := sH ψH) α).symm
    _ = algebraMap ℤ ℂ (n * b) := hb



end CharacterizationOfCharacters

end Representation
