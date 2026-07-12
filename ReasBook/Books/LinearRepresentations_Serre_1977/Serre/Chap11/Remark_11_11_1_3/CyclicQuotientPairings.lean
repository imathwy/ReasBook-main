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

noncomputable section

universe v

namespace Representation

section CharacterizationOfCharacters

open scoped Pointwise Representation SubgroupInduction TensorProduct

variable {G : Type} [Group G] [Finite G]
variable {A : Type v} [CommRing A]

local notation:max s " •ᶜ " H => (MulAut.conj s • H : Subgroup G)

/-- Helper for Remark 11-11.1-3: every subgroup of a finite group is finite. -/
local instance fintypeHelperLocalCyclicQuotientPairings1 (H : Subgroup G) : Fintype H := Fintype.ofFinite H

/-- Helper for Remark 11-11.1-3: the degree-one characters of a finite group form a finite type. -/
noncomputable local instance fintypeHelperLocalCyclicQuotientPairings2
    (Q : Type*) [Group Q] [Finite Q] : Fintype (Q →* ℂˣ) := Fintype.ofFinite _

attribute [local instance] Classical.propDecidable
/-- Helper for Remark 11-11.1-3: the same chosen-coatom identity can be read in reverse. If the
coatom induced-trivial pairing and the faithful cyclic layer are both `n`-multiples, then the
distinguished ambient difference term is an `n`-multiple as well. -/
theorem difference_divisible_of_kernel_eq_chosen_coatom_of_faithful_cyclic_layer_divisible
    {H0 : Type} [Group H0] [Finite H0] {n : ℤ}
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
          ∑ γ ∈ ((Finset.univ.erase
              (QuotientGroup.lift δ.ker δ (show δ.ker ≤ δ.ker from le_rfl))).filter
            fun γ => γ.ker = ⊥),
            ⟪(((γ.comp (QuotientGroup.mk' δ.ker)).toCharacterRing - 1 : R(H0)) :
                  H0 → ℂ),
                (ξH : H0 → ℂ)⟫ =
          algebraMap ℤ ℂ (n * bC)) :
    ∃ bδ : ℤ,
      ⟪(((δ.toCharacterRing - 1 : R(H0)) : H0 → ℂ)), (ξH : H0 → ℂ)⟫ =
        algebraMap ℤ ℂ (n * bδ) := by
  classical
  subst hEq
  let δq : (H0 ⧸ δ.ker) →* ℂˣ :=
    QuotientGroup.lift δ.ker δ (show δ.ker ≤ δ.ker from le_rfl)
  let term : ((H0 ⧸ δ.ker) →* ℂˣ) → ℂ := fun γ ↦
    ⟪(((γ.comp (QuotientGroup.mk' δ.ker)).toCharacterRing - 1 : R(H0)) : H0 → ℂ),
        (ξH : H0 → ℂ)⟫
  obtain ⟨_, hδq_ne, _, _⟩ := kernel_quotient_distinguished_character_data δ hδ
  rcases hMpair with ⟨bM, hbM⟩
  rcases hcyclic with ⟨bC, hbC⟩
  have hsplit :
      ∑ γ ∈ Finset.univ.erase δq, term γ =
        ∑ γ ∈ ((Finset.univ.erase δq).filter fun γ => γ.ker = ⊥), term γ +
          ∑ γ ∈ ((Finset.univ.erase δq).filter fun γ => γ.ker ≠ ⊥), term γ := by
    -- Split the erased quotient-character family into faithful and nonfaithful branches.
    simpa using
      (Finset.sum_filter_add_sum_filter_not
        (s := Finset.univ.erase δq)
        (f := term)
        (p := fun γ : (H0 ⧸ δ.ker) →* ℂˣ => γ.ker = ⊥)).symm
  have hnonfaithful :
      ∑ γ ∈ ((Finset.univ.erase δq).filter fun γ => γ.ker ≠ ⊥), term γ = 0 := by
    -- On the prime quotient above the chosen coatom, the erased nonfaithful branch still vanishes.
    simpa [δq, term] using
      prime_coatom_nonfaithful_erased_branch_vanishes
        (M := δ.ker) hprime δq hδq_ne ξH
  have hrewrite :
      ⟪(Subgroup.characterRingInduction δ.ker (1 : R(δ.ker)) : H0 → ℂ), (ξH : H0 → ℂ)⟫ =
        ((δ.ker.index : ℂ) * ⟪((1 : R(H0)) : H0 → ℂ), (ξH : H0 → ℂ)⟫ +
            ∑ γ ∈ ((Finset.univ.erase δq).filter fun γ => γ.ker = ⊥), term γ) +
          ⟪(((δ.toCharacterRing - 1 : R(H0)) : H0 → ℂ)), (ξH : H0 → ℂ)⟫ := by
    -- Rewrite the coatom induced-trivial pairing by isolating the faithful erased branch and then
    -- discard the prime-quotient nonfaithful branch.
    calc
      ⟪(Subgroup.characterRingInduction δ.ker (1 : R(δ.ker)) : H0 → ℂ), (ξH : H0 → ℂ)⟫ =
          (δ.ker.index : ℂ) * ⟪((1 : R(H0)) : H0 → ℂ), (ξH : H0 → ℂ)⟫ +
            ⟪(((δ.toCharacterRing - 1 : R(H0)) : H0 → ℂ)), (ξH : H0 → ℂ)⟫ +
              ∑ γ ∈ Finset.univ.erase δq, term γ := by
                simpa [δq, term] using
                  kernel_induced_pairing_decomposes_with_distinguished_difference
                    (β := δ)
                    (ξ := ξH)
      _ =
          (δ.ker.index : ℂ) * ⟪((1 : R(H0)) : H0 → ℂ), (ξH : H0 → ℂ)⟫ +
            ⟪(((δ.toCharacterRing - 1 : R(H0)) : H0 → ℂ)), (ξH : H0 → ℂ)⟫ +
              (∑ γ ∈ ((Finset.univ.erase δq).filter fun γ => γ.ker = ⊥), term γ +
                ∑ γ ∈ ((Finset.univ.erase δq).filter fun γ => γ.ker ≠ ⊥), term γ) := by
                  rw [hsplit]
      _ =
          (δ.ker.index : ℂ) * ⟪((1 : R(H0)) : H0 → ℂ), (ξH : H0 → ℂ)⟫ +
            ⟪(((δ.toCharacterRing - 1 : R(H0)) : H0 → ℂ)), (ξH : H0 → ℂ)⟫ +
              ∑ γ ∈ ((Finset.univ.erase δq).filter fun γ => γ.ker = ⊥), term γ := by
                  rw [hnonfaithful]
                  simp
      _ =
          ((δ.ker.index : ℂ) * ⟪((1 : R(H0)) : H0 → ℂ), (ξH : H0 → ℂ)⟫ +
              ∑ γ ∈ ((Finset.univ.erase δq).filter fun γ => γ.ker = ⊥), term γ) +
            ⟪(((δ.toCharacterRing - 1 : R(H0)) : H0 → ℂ)), (ξH : H0 → ℂ)⟫ := by
                  abel
  have htarget :
      ⟪(((δ.toCharacterRing - 1 : R(H0)) : H0 → ℂ)), (ξH : H0 → ℂ)⟫ =
        ⟪(Subgroup.characterRingInduction δ.ker (1 : R(δ.ker)) : H0 → ℂ), (ξH : H0 → ℂ)⟫ -
          ((δ.ker.index : ℂ) * ⟪((1 : R(H0)) : H0 → ℂ), (ξH : H0 → ℂ)⟫ +
            ∑ γ ∈ ((Finset.univ.erase δq).filter fun γ => γ.ker = ⊥), term γ) := by
    -- Move the faithful cyclic layer to the right to isolate the distinguished difference term.
    exact eq_sub_iff_add_eq.mpr <| by
      simpa [add_comm, add_left_comm, add_assoc] using hrewrite.symm
  refine ⟨bM - bC, ?_⟩
  -- Subtract the faithful cyclic-layer witness from the coatom induced-trivial witness.
  calc
    ⟪(((δ.toCharacterRing - 1 : R(H0)) : H0 → ℂ)), (ξH : H0 → ℂ)⟫ =
      ⟪(Subgroup.characterRingInduction δ.ker (1 : R(δ.ker)) : H0 → ℂ), (ξH : H0 → ℂ)⟫ -
        ((δ.ker.index : ℂ) * ⟪((1 : R(H0)) : H0 → ℂ), (ξH : H0 → ℂ)⟫ +
          ∑ γ ∈ ((Finset.univ.erase δq).filter fun γ => γ.ker = ⊥), term γ) := htarget
    _ = algebraMap ℤ ℂ (n * bM) - algebraMap ℤ ℂ (n * bC) := by
          rw [hbM, hbC]
    _ = algebraMap ℤ ℂ (n * (bM - bC)) := by
          simp [Int.cast_mul, Int.cast_sub, sub_eq_add_neg, mul_add, mul_assoc]

/-- Helper for Remark 11-11.1-3: if `δ.ker < M` and `β` is a nontrivial character of the prime
coatom quotient `H0 ⧸ M`, then the smaller-kernel package for the lift `β.comp mk' M` already
supplies the ambient difference-pairing divisibility witness needed in the strict branch. -/
theorem prime_coatom_lift_difference_pairing_divisible_from_smaller_kernel_package
    {H0 : Type} [Group H0] [Finite H0] {n : ℤ}
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
            ∑ γ ∈
                ((Finset.univ.erase
                    (QuotientGroup.lift ε.ker ε (show ε.ker ≤ ε.ker from le_rfl))).filter
                  fun γ => γ.ker = ⊥),
                ⟪(((γ.comp (QuotientGroup.mk' ε.ker)).toCharacterRing - 1 : R(H0)) :
                      H0 → ℂ),
                    (ξH : H0 → ℂ)⟫ =
              algebraMap ℤ ℂ (n * bC))
    (β : (H0 ⧸ M) →* ℂˣ) (hβ : β ≠ 1) :
    ∃ bβ : ℤ,
      ⟪(((β.comp (QuotientGroup.mk' M)).toCharacterRing - 1 : R(H0)) : H0 → ℂ),
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
          ∑ γ ∈
              ((Finset.univ.erase
                  (QuotientGroup.lift ε.ker ε (show ε.ker ≤ ε.ker from le_rfl))).filter
                fun γ => γ.ker = ⊥),
              ⟪(((γ.comp (QuotientGroup.mk' ε.ker)).toCharacterRing - 1 : R(H0)) :
                    H0 → ℂ),
                  (ξH : H0 → ℂ)⟫ =
            algebraMap ℤ ℂ (n * bC) := hm ε hε_ne hε_lt
  -- Convert the smaller-kernel faithful cyclic-layer package for the lift `ε` into the desired
  -- ambient difference witness.
  simpa [ε] using
    difference_divisible_of_kernel_eq_chosen_coatom_of_faithful_cyclic_layer_divisible
      ε hε_ne M ξH hε_ker hprime hMpair hεcyclic

/-- Helper for Remark 11-11.1-3: after isolating the distinguished quotient character `βq`, the
nonfaithful erased quotient-character summands are exactly the smaller-kernel branch owned by the
induction hypothesis, together with the trivial lifted branch. -/
theorem nonfaithful_erased_quotient_sum_divisible
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
          ⟪(((δ.toCharacterRing - 1 : R(H.1)) : H.1 → ℂ)),
              ((sH ψH : R(H.1)) : H.1 → ℂ)⟫ =
            algebraMap ℤ ℂ (n * b)) :
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
    ∃ bNF : ℤ,
      ∑ γ ∈ ((Finset.univ.erase βq).filter fun γ => γ.ker ≠ ⊥), term γ =
        algebraMap ℤ ℂ (n * bNF) := by
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
  apply finset_sum_int_multiples
  intro γ hγ
  have hγker : γ.ker ≠ ⊥ := by
    simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_univ, true_and] at hγ
    exact hγ.2
  by_cases hδ : γ.comp (QuotientGroup.mk' β.ker) = 1
  · -- The trivial lifted branch contributes the zero difference character.
    simpa [term] using
      erased_quotient_character_difference_divisible_of_comp_eq_one
        X hXelem (t := t) (n := n) H sH β γ hδ
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
theorem proper_induced_trivial_pairing_divisible_of_local_proper_branch
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
  have hchar : ((1 : J →* ℂˣ).toRepresentation.character) = (1 : J → ℂ) := by
    ext k
    simp
  simpa [hchar] using
    proper_induced_pairing_divisible_of_transport_pairing_int_divisible
      X hXelem hdx H sH hsH J (1 : J →* ℂˣ) (hproper J hJ (1 : J →* ℂˣ))

/-- Helper for Remark 11-11.1-3: multiplying a proper induced-trivial pairing by an integral
coefficient preserves the `n`-divisibility witness coming from the local proper branch. -/
theorem int_multiple_of_proper_induced_trivial_pairing_divisible_of_local_proper_branch
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


end CharacterizationOfCharacters

end Representation
