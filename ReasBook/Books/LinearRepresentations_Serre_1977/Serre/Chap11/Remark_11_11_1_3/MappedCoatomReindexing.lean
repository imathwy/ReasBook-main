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

noncomputable section

universe v

namespace Representation

section CharacterizationOfCharacters

open scoped Pointwise Representation SubgroupInduction TensorProduct

variable {G : Type} [Group G] [Finite G]
variable {A : Type v} [CommRing A]

local notation:max s " •ᶜ " H => (MulAut.conj s • H : Subgroup G)

/-- Helper for Remark 11-11.1-3: every subgroup of a finite group is finite. -/
local instance fintypeHelperLocalMappedCoatomReindexing1 (H : Subgroup G) : Fintype H := Fintype.ofFinite H

/-- Helper for Remark 11-11.1-3: the degree-one characters of a finite group form a finite type. -/
noncomputable local instance fintypeHelperLocalMappedCoatomReindexingA
    (Q : Type*) [Group Q] [Finite Q] : Fintype (Q →* ℂˣ) := Fintype.ofFinite _

/-- Helper for Remark 11-11.1-3: quotients of finite groups are finite types. -/
noncomputable local instance fintypeHelperLocalMappedCoatomReindexingB
    (Q : Type*) [Group Q] [Finite Q] (M : Subgroup Q) : Fintype (Q ⧸ M) :=
  Fintype.ofFinite _

/-- Helper for Remark 11-11.1-3: one canonical classical decidable equality for characters. -/
noncomputable local instance (priority := 2000) fintypeHelperLocalMappedCoatomReindexingC
    (Q : Type*) [Group Q] : DecidableEq (Q →* ℂˣ) := Classical.decEq _

attribute [local instance] Classical.propDecidable
/-- Helper for Remark 11-11.1-3: the exact mapped-coatom slice can be reindexed by the nontrivial
characters of the direct prime quotient `H0 ⧸ M` using the transported lift map through the third
isomorphism. -/
theorem strict_branch_exact_slice_sum_reindex
    {H0 : Type} [Group H0] [Finite H0]
    (δ : H0 →* ℂˣ)
    (M : Subgroup H0) [M.Normal]
    (hδker_lt_M : δ.ker < M)
    (hprime : (Nat.card (H0 ⧸ M)).Prime)
    (F : ((H0 ⧸ δ.ker) →* ℂˣ) → ℂ) :
    let δq : (H0 ⧸ δ.ker) →* ℂˣ :=
      QuotientGroup.lift δ.ker δ (show δ.ker ≤ δ.ker from le_rfl)
    let Mq : Subgroup (H0 ⧸ δ.ker) := M.map (QuotientGroup.mk' δ.ker)
    let e : ((H0 ⧸ δ.ker) ⧸ Mq) ≃* H0 ⧸ M :=
      QuotientGroup.quotientQuotientEquivQuotient δ.ker M hδker_lt_M.le
    let exactSlice : Finset ((H0 ⧸ δ.ker) →* ℂˣ) :=
      ((((Finset.univ.erase δq).filter fun γ => γ.ker ≠ ⊥).erase 1).filter
        fun γ => γ.ker = Mq)
    let liftChar : ((H0 ⧸ M) →* ℂˣ) → ((H0 ⧸ δ.ker) →* ℂˣ) := fun β ↦
      (((β.comp e.toMonoidHom).comp (QuotientGroup.mk' Mq)) : (H0 ⧸ δ.ker) →* ℂˣ)
    ∑ γ ∈ exactSlice, F γ =
      ∑ β ∈ Finset.univ.erase (1 : (H0 ⧸ M) →* ℂˣ), F (liftChar β) := by
  classical
  let δq : (H0 ⧸ δ.ker) →* ℂˣ :=
    QuotientGroup.lift δ.ker δ (show δ.ker ≤ δ.ker from le_rfl)
  let Mq : Subgroup (H0 ⧸ δ.ker) := M.map (QuotientGroup.mk' δ.ker)
  let e : ((H0 ⧸ δ.ker) ⧸ Mq) ≃* H0 ⧸ M :=
    QuotientGroup.quotientQuotientEquivQuotient δ.ker M hδker_lt_M.le
  let exactSlice : Finset ((H0 ⧸ δ.ker) →* ℂˣ) :=
    ((((Finset.univ.erase δq).filter fun γ => γ.ker ≠ ⊥).erase 1).filter
      fun γ => γ.ker = Mq)
  let liftChar : ((H0 ⧸ M) →* ℂˣ) → ((H0 ⧸ δ.ker) →* ℂˣ) := fun β ↦
    (((β.comp e.toMonoidHom).comp (QuotientGroup.mk' Mq)) : (H0 ⧸ δ.ker) →* ℂˣ)
  have hlift_mem :
      ∀ {β : (H0 ⧸ M) →* ℂˣ}, β ∈ Finset.univ.erase (1 : (H0 ⧸ M) →* ℂˣ) →
        liftChar β ∈ exactSlice := by
    intro β hβ
    -- The forward exact-slice membership bridge turns the erased direct quotient family into the
    -- exact mapped-coatom slice.
    exact
      strict_branch_lifted_quotient_character_mem_exact_slice
        (δ := δ)
        (M := M)
        hδker_lt_M
        hprime
        β
        (by simpa [Finset.mem_erase] using hβ)
  have hlift_injective :
      ∀ {β₁ β₂ : (H0 ⧸ M) →* ℂˣ},
        liftChar β₁ = liftChar β₂ → β₁ = β₂ := by
    intro β₁ β₂ hEq
    refine MonoidHom.ext fun x ↦ ?_
    obtain ⟨y, rfl⟩ := e.surjective x
    obtain ⟨z, rfl⟩ := QuotientGroup.mk'_surjective Mq y
    -- Evaluate the lifted equality on a representative of the iterated quotient class to recover
    -- equality of the original direct quotient characters.
    simpa [liftChar, e] using DFunLike.congr_fun hEq z
  have hexact_surjective :
      ∀ {γ : (H0 ⧸ δ.ker) →* ℂˣ}, γ ∈ exactSlice →
        ∃ β : (H0 ⧸ M) →* ℂˣ,
          β ∈ Finset.univ.erase (1 : (H0 ⧸ M) →* ℂˣ) ∧ liftChar β = γ := by
    intro γ hγ
    rcases
        strict_branch_exact_slice_member_eq_lifted_quotient_character
          (δ := δ)
          (M := M)
          hδker_lt_M
          (by simpa [exactSlice] using hγ) with
      ⟨β, hβ_ne, hγ_eq⟩
    refine ⟨β, Finset.mem_erase.mpr ⟨hβ_ne, by simp⟩, ?_⟩
    -- The reverse exact-slice parametrization gives the inverse map for the reindexing bijection.
    simpa [liftChar, e, Mq] using hγ_eq.symm
  have hsum :
      ∑ β ∈ Finset.univ.erase (1 : (H0 ⧸ M) →* ℂˣ), F (liftChar β) =
        ∑ γ ∈ exactSlice, F γ := by
    refine Finset.sum_bij (fun β _ ↦ liftChar β) ?_ ?_ ?_ ?_
    · intro β hβ
      exact hlift_mem hβ
    · intro β₁ hβ₁ β₂ hβ₂ hEq
      exact hlift_injective hEq
    · intro γ hγ
      rcases hexact_surjective hγ with ⟨β, hβ, hβγ⟩
      exact ⟨β, hβ, hβγ⟩
    · intro β hβ
      rfl
  exact hsum.symm

/-- Helper for Remark 11-11.1-3: after reindexing the exact mapped-coatom slice by the nontrivial
characters of `H0 ⧸ M`, each term is exactly the chosen-coatom induced-trivial pairing minus the
direct quotient-character difference term. -/
theorem strict_branch_reindexed_exact_slice_term_eq_coatom_pairing_minus_direct_difference
    {H0 : Type} [Group H0] [Finite H0]
    (δ : H0 →* ℂˣ)
    (M : Subgroup H0) [M.Normal]
    (hδker_lt_M : δ.ker < M)
    (hprime : (Nat.card (H0 ⧸ M)).Prime)
    (ξH : R(H0))
    {β : (H0 ⧸ M) →* ℂˣ}
    (hβ : β ∈ Finset.univ.erase (1 : (H0 ⧸ M) →* ℂˣ)) :
    let Mq : Subgroup (H0 ⧸ δ.ker) := M.map (QuotientGroup.mk' δ.ker)
    let e : ((H0 ⧸ δ.ker) ⧸ Mq) ≃* H0 ⧸ M :=
      QuotientGroup.quotientQuotientEquivQuotient δ.ker M hδker_lt_M.le
    let liftChar : ((H0 ⧸ M) →* ℂˣ) → ((H0 ⧸ δ.ker) →* ℂˣ) := fun β ↦
      (((β.comp e.toMonoidHom).comp (QuotientGroup.mk' Mq)) : (H0 ⧸ δ.ker) →* ℂˣ)
    let smallerTop : ((H0 ⧸ δ.ker) →* ℂˣ) → ℂ := fun γ ↦
      let ε : H0 →* ℂˣ := γ.comp (QuotientGroup.mk' δ.ker)
      let ηε : R(H0 ⧸ ε.ker) :=
        (ε.ker.index : ℤ) • (1 : R(H0 ⧸ ε.ker)) +
          Finset.sum
            (((Finset.univ.erase
                (QuotientGroup.lift ε.ker ε (show ε.ker ≤ ε.ker from le_rfl))).filter
              fun θ => θ.ker = ⊥))
            (fun θ ↦ ((θ.toCharacterRing - 1 : R(H0 ⧸ ε.ker))))
      quotient_pullback_pairing_linearMap ε ξH ηε
    smallerTop (liftChar β) =
      ⟪(Subgroup.characterRingInduction M (1 : R(M)) : H0 → ℂ), (ξH : H0 → ℂ)⟫ -
        ⟪(((β.comp (QuotientGroup.mk' M)).toCharacterRing - 1 : R(H0)) : H0 → ℂ),
            (ξH : H0 → ℂ)⟫ := by
  classical
  dsimp
  let Mq : Subgroup (H0 ⧸ δ.ker) := M.map (QuotientGroup.mk' δ.ker)
  let e : ((H0 ⧸ δ.ker) ⧸ Mq) ≃* H0 ⧸ M :=
    QuotientGroup.quotientQuotientEquivQuotient δ.ker M hδker_lt_M.le
  let liftChar : ((H0 ⧸ M) →* ℂˣ) → ((H0 ⧸ δ.ker) →* ℂˣ) := fun β ↦
    (((β.comp e.toMonoidHom).comp (QuotientGroup.mk' Mq)) : (H0 ⧸ δ.ker) →* ℂˣ)
  let smallerTop : ((H0 ⧸ δ.ker) →* ℂˣ) → ℂ := fun γ ↦
    let ε : H0 →* ℂˣ := γ.comp (QuotientGroup.mk' δ.ker)
    let ηε : R(H0 ⧸ ε.ker) :=
      (ε.ker.index : ℤ) • (1 : R(H0 ⧸ ε.ker)) +
        ∑ θ ∈
            ((Finset.univ.erase
                (QuotientGroup.lift ε.ker ε (show ε.ker ≤ ε.ker from le_rfl))).filter
              fun θ => θ.ker = ⊥),
            ((θ.toCharacterRing - 1 : R(H0 ⧸ ε.ker)))
    quotient_pullback_pairing_linearMap ε ξH ηε
  let γ : (H0 ⧸ δ.ker) →* ℂˣ := liftChar β
  have hγ_mem :
      γ ∈ ((((Finset.univ.erase
          (QuotientGroup.lift δ.ker δ (show δ.ker ≤ δ.ker from le_rfl))).filter
        fun γ => γ.ker ≠ ⊥).erase 1).filter
        fun γ => γ.ker = Mq) := by
    -- Reindex the exact slice by the direct prime-quotient characters before applying the
    -- kernel-equality faithful-layer identity.
    simpa [γ, liftChar, Mq, e] using
      strict_branch_lifted_quotient_character_mem_exact_slice
        (δ := δ)
        (M := M)
        hδker_lt_M
        hprime
        β
        (by simpa [Finset.mem_erase] using hβ)
  have hγker :
      (γ.comp (QuotientGroup.mk' δ.ker)).ker = M := by
    -- Exact-slice membership records that the pulled-back ambient kernel is the chosen coatom.
    exact
      (strict_branch_exact_mapped_coatom_slice_member_data
        (δ := δ)
        (M := M)
        hδker_lt_M
        hγ_mem).2
  let ε : H0 →* ℂˣ := γ.comp (QuotientGroup.mk' δ.ker)
  have hε_eq : ε = β.comp (QuotientGroup.mk' M) := by
    -- Transport the lifted exact-slice character back across the third-isomorphism comparison.
    simpa [ε, γ, liftChar, Mq, e, MonoidHom.comp_assoc] using
      (iterated_quotient_character_pullback_eq_direct_pullback
        (δ := δ)
        (M := M)
        hδker_lt_M.le
        (β := β.comp e.toMonoidHom))
  have hε_ne : ε ≠ 1 := by
    -- Precomposing with the quotient map by `M` preserves nontriviality of the direct quotient
    -- character.
    rw [hε_eq]
    intro hε
    have hβ_one : β = 1 := by
      refine MonoidHom.ext fun x ↦ ?_
      obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective M x
      simpa using DFunLike.congr_fun hε y
    exact (Finset.mem_erase.mp hβ).1 hβ_one
  -- Apply the kernel-equality faithful cyclic-layer identity to the lifted character and then
  -- rewrite the ambient difference term back to the direct quotient side.
  calc
    smallerTop (liftChar β) =
      ⟪(Subgroup.characterRingInduction M (1 : R(M)) : H0 → ℂ), (ξH : H0 → ℂ)⟫ -
        ⟪(((ε.toCharacterRing - 1 : R(H0)) : H0 → ℂ)), (ξH : H0 → ℂ)⟫ := by
          have htop :=
            (faithful_quotient_top_layer_eq_quotient_pullback_pairing
              (β := ε) (ξ := ξH)).symm
          have hlayer :=
            faithful_cyclic_layer_pairing_eq_kernel_induced_minus_distinguished_difference
              (δ := ε)
              (hδ := hε_ne)
              (M := M)
              (ξH := ξH)
              hγker
              hprime
          exact htop.trans hlayer
    _ =
      ⟪(Subgroup.characterRingInduction M (1 : R(M)) : H0 → ℂ), (ξH : H0 → ℂ)⟫ -
        ⟪(((β.comp (QuotientGroup.mk' M)).toCharacterRing - 1 : R(H0)) : H0 → ℂ),
            (ξH : H0 → ℂ)⟫ := by
          rw [hε_eq]

/-- Helper for Remark 11-11.1-3: the transported mapped-coatom quotient-difference family is
exactly the ambient coatom pairing minus the index-scaled trivial pullback branch. This isolates
the direct prime-quotient difference sum before the final exact-slice counting step. -/
theorem strict_branch_prime_quotient_difference_sum_eq_coatom_pairing_sub_index_trivial
    {H0 : Type} [Group H0] [Finite H0]
    (δ : H0 →* ℂˣ)
    (M : Subgroup H0) [M.Normal]
    (hδker_lt_M : δ.ker < M)
    (hprime : (Nat.card (H0 ⧸ M)).Prime)
    (ξH : R(H0)) :
    ∑ β ∈ Finset.univ.erase (1 : (H0 ⧸ M) →* ℂˣ),
      ⟪(((β.comp (QuotientGroup.mk' M)).toCharacterRing - 1 : R(H0)) : H0 → ℂ),
          (ξH : H0 → ℂ)⟫ =
      ⟪(Subgroup.characterRingInduction M (1 : R(M)) : H0 → ℂ), (ξH : H0 → ℂ)⟫ -
        (M.index : ℂ) * quotient_pullback_pairing_linearMap δ ξH (1 : R(H0 ⧸ δ.ker)) := by
  classical
  let Mq : Subgroup (H0 ⧸ δ.ker) := M.map (QuotientGroup.mk' δ.ker)
  have hmapped_block :
      quotient_pullback_pairing_linearMap δ ξH
          (Subgroup.characterRingInduction Mq (1 : R(Mq)) -
            ∑ β : ((H0 ⧸ δ.ker) ⧸ Mq) →* ℂˣ,
              (((β.comp (QuotientGroup.mk' Mq)).toCharacterRing - 1 : R(H0 ⧸ δ.ker)))) =
        (M.index : ℂ) * quotient_pullback_pairing_linearMap δ ξH (1 : R(H0 ⧸ δ.ker)) := by
    -- Keep the mapped-coatom package in the quotient-pullback form before expanding it linearly.
    simpa [Mq] using
      strict_branch_etaM_pairing_eq_mapped_coatom_index_trivial
        (δ := δ)
        (M := M)
        hδker_lt_M
        (ξH := ξH)
  have hmapped_block_linearized :
      quotient_pullback_pairing_linearMap δ ξH
          (Subgroup.characterRingInduction Mq (1 : R(Mq))) -
        ∑ β : ((H0 ⧸ δ.ker) ⧸ Mq) →* ℂˣ,
          quotient_pullback_pairing_linearMap δ ξH
            (((β.comp (QuotientGroup.mk' Mq)).toCharacterRing - 1 : R(H0 ⧸ δ.ker))) =
      (M.index : ℂ) * quotient_pullback_pairing_linearMap δ ξH (1 : R(H0 ⧸ δ.ker)) := by
    -- Expand the quotient pullback pairing across the single mapped-coatom subtraction.
    have h := hmapped_block
    rw [map_sub, map_sum] at h
    simpa using h
  have hiterated_transport :
      ∑ β : ((H0 ⧸ δ.ker) ⧸ Mq) →* ℂˣ,
        quotient_pullback_pairing_linearMap δ ξH
          (((β.comp (QuotientGroup.mk' Mq)).toCharacterRing - 1 : R(H0 ⧸ δ.ker))) =
      ∑ β ∈ ((Finset.univ.erase (1 : (H0 ⧸ M) →* ℂˣ)).filter fun β => β.ker = ⊥),
        ⟪(((β.comp (QuotientGroup.mk' M)).toCharacterRing - 1 : R(H0)) : H0 → ℂ),
            (ξH : H0 → ℂ)⟫ := by
    -- Transport the iterated quotient family across Noether's third isomorphism.
    simpa [Mq] using
      strict_branch_iterated_difference_sum_eq_prime_quotient_faithful_sum
        (δ := δ)
        (M := M)
        hδker_lt_M
        hprime
        (ξH := ξH)
  have hprime_sum :
      ∑ β ∈ Finset.univ.erase (1 : (H0 ⧸ M) →* ℂˣ),
        ⟪(((β.comp (QuotientGroup.mk' M)).toCharacterRing - 1 : R(H0)) : H0 → ℂ),
            (ξH : H0 → ℂ)⟫ =
      quotient_pullback_pairing_linearMap δ ξH
          (Subgroup.characterRingInduction Mq (1 : R(Mq))) -
        (M.index : ℂ) * quotient_pullback_pairing_linearMap δ ξH (1 : R(H0 ⧸ δ.ker)) := by
    -- Rewrite the transported prime-quotient family as the residual term of the mapped-coatom
    -- package.
    calc
      ∑ β ∈ Finset.univ.erase (1 : (H0 ⧸ M) →* ℂˣ),
          ⟪(((β.comp (QuotientGroup.mk' M)).toCharacterRing - 1 : R(H0)) : H0 → ℂ),
              (ξH : H0 → ℂ)⟫ =
        ∑ β ∈ ((Finset.univ.erase (1 : (H0 ⧸ M) →* ℂˣ)).filter fun β => β.ker = ⊥),
            ⟪(((β.comp (QuotientGroup.mk' M)).toCharacterRing - 1 : R(H0)) : H0 → ℂ),
                (ξH : H0 → ℂ)⟫ := by
              simpa [prime_quotient_faithful_filter_eq_erase_one (M := M) hprime]
      _ =
        ∑ β : ((H0 ⧸ δ.ker) ⧸ Mq) →* ℂˣ,
          quotient_pullback_pairing_linearMap δ ξH
            (((β.comp (QuotientGroup.mk' Mq)).toCharacterRing - 1 : R(H0 ⧸ δ.ker))) := by
              rw [hiterated_transport]
      _ =
        quotient_pullback_pairing_linearMap δ ξH
            (Subgroup.characterRingInduction Mq (1 : R(Mq))) -
          (M.index : ℂ) * quotient_pullback_pairing_linearMap δ ξH (1 : R(H0 ⧸ δ.ker)) := by
            calc
              ∑ β : ((H0 ⧸ δ.ker) ⧸ Mq) →* ℂˣ,
                  quotient_pullback_pairing_linearMap δ ξH
                    (((β.comp (QuotientGroup.mk' Mq)).toCharacterRing - 1 : R(H0 ⧸ δ.ker))) =
                quotient_pullback_pairing_linearMap δ ξH
                    (Subgroup.characterRingInduction Mq (1 : R(Mq))) -
                  (quotient_pullback_pairing_linearMap δ ξH
                      (Subgroup.characterRingInduction Mq (1 : R(Mq))) -
                    ∑ β : ((H0 ⧸ δ.ker) ⧸ Mq) →* ℂˣ,
                      quotient_pullback_pairing_linearMap δ ξH
                        (((β.comp (QuotientGroup.mk' Mq)).toCharacterRing - 1 :
                            R(H0 ⧸ δ.ker)))) := by
                              abel
              _ =
                quotient_pullback_pairing_linearMap δ ξH
                    (Subgroup.characterRingInduction Mq (1 : R(Mq))) -
                  (M.index : ℂ) * quotient_pullback_pairing_linearMap δ ξH (1 : R(H0 ⧸ δ.ker)) := by
                    rw [hmapped_block_linearized]
  -- Replace the mapped-coatom quotient induction by the ambient coatom pairing.
  calc
    ∑ β ∈ Finset.univ.erase (1 : (H0 ⧸ M) →* ℂˣ),
        ⟪(((β.comp (QuotientGroup.mk' M)).toCharacterRing - 1 : R(H0)) : H0 → ℂ),
            (ξH : H0 → ℂ)⟫ =
      quotient_pullback_pairing_linearMap δ ξH
          (Subgroup.characterRingInduction Mq (1 : R(Mq))) -
        (M.index : ℂ) * quotient_pullback_pairing_linearMap δ ξH (1 : R(H0 ⧸ δ.ker)) := hprime_sum
    _ =
      ⟪(Subgroup.characterRingInduction M (1 : R(M)) : H0 → ℂ), (ξH : H0 → ℂ)⟫ -
        (M.index : ℂ) * quotient_pullback_pairing_linearMap δ ξH (1 : R(H0 ⧸ δ.ker)) := by
          rw [strict_branch_mapped_coatom_pullback_pairing_eq_ambient_coatom_pairing
            (δ := δ)
            (M := M)
            hδker_lt_M.le
            ξH]

/-- Helper for Remark 11-11.1-3: the nontrivial linear characters of the prime quotient
`H0 ⧸ M` are exactly the `M.index - 1` elements of the erased finite dual. -/
theorem strict_branch_nontrivial_prime_quotient_character_count
    {H0 : Type} [Group H0] [Finite H0]
    (δ : H0 →* ℂˣ)
    (M : Subgroup H0) [M.Normal]
    (hδker_lt_M : δ.ker < M) :
    ((Finset.univ.erase (1 : (H0 ⧸ M) →* ℂˣ)).card : ℂ) = (M.index : ℂ) - 1 := by
  classical
  have hδ : δ ≠ 1 := by
    -- A trivial ambient character would have kernel `⊤`, contradicting the strict branch.
    intro hδ
    have hker_top : δ.ker = ⊤ := by
      ext x
      simp [hδ, MonoidHom.mem_ker]
    have hnot_lt : ¬ δ.ker < M := by
      simpa [hker_top] using (show ¬ (⊤ : Subgroup H0) < M from not_lt_of_ge le_top)
    exact hnot_lt hδker_lt_M
  let Mq : Subgroup (H0 ⧸ δ.ker) := M.map (QuotientGroup.mk' δ.ker)
  let e : ((H0 ⧸ δ.ker) ⧸ Mq) ≃* H0 ⧸ M :=
    QuotientGroup.quotientQuotientEquivQuotient δ.ker M hδker_lt_M.le
  let q : (H0 ⧸ δ.ker) →* H0 ⧸ M := e.toMonoidHom.comp (QuotientGroup.mk' Mq)
  have hq_surj : Function.Surjective q := by
    intro x
    obtain ⟨y, rfl⟩ := e.surjective x
    obtain ⟨z, rfl⟩ := QuotientGroup.mk'_surjective Mq y
    exact ⟨z, rfl⟩
  have hcyc_quot : IsCyclic (H0 ⧸ δ.ker) :=
    kernel_quotient_isCyclic_of_nontrivial_character δ hδ
  have hcyc_prime : IsCyclic (H0 ⧸ M) := isCyclic_of_surjective q hq_surj
  letI : CommGroup (H0 ⧸ M) := IsCyclic.commGroup
  letI : Fintype ((H0 ⧸ M) →* ℂˣ) := linearCharacterFintype
  have hcard_sub :
      ((Nat.card (H0 ⧸ M) - 1 : ℕ) : ℂ) = (Nat.card (H0 ⧸ M) : ℂ) - 1 := by
    exact_mod_cast Nat.cast_sub (Nat.succ_le_of_lt Nat.card_pos)
  -- Count the erased finite dual by duality for the cyclic quotient `H0 ⧸ M`.
  calc
    ((Finset.univ.erase (1 : (H0 ⧸ M) →* ℂˣ)).card : ℂ) =
      (Fintype.card ((H0 ⧸ M) →* ℂˣ) - 1 : ℂ) := by
        rw [Finset.card_erase_of_mem (Finset.mem_univ (1 : (H0 ⧸ M) →* ℂˣ)),
          Finset.card_univ]
        push_cast [Nat.cast_sub
          (Nat.succ_le_of_lt (Fintype.card_pos (α := (H0 ⧸ M) →* ℂˣ)))]
        ring
    _ = (Nat.card ((H0 ⧸ M) →* ℂˣ) - 1 : ℂ) := by
        simp [Nat.card_eq_fintype_card]
    _ = (Nat.card (H0 ⧸ M) - 1 : ℂ) := by
        have hcardEq := CommGroup.card_monoidHom_of_hasEnoughRootsOfUnity (H0 ⧸ M) ℂ
        rw [hcardEq]
    _ = (Nat.card (H0 ⧸ M) : ℂ) - 1 := rfl
    _ = (M.index : ℂ) - 1 := by
        simp [M.index_eq_card]

/-- Helper for Remark 11-11.1-3: a constant coatom-pairing term summed over the erased direct
quotient dual is just the cardinality of that dual times the constant. -/
theorem strict_branch_constant_coatom_sum_eq_card_mul
    {H0 : Type} [Group H0] [Finite H0]
    (M : Subgroup H0) [M.Normal]
    (z : ℂ) :
    ∑ _β ∈ Finset.univ.erase (1 : (H0 ⧸ M) →* ℂˣ), z =
      (((Finset.univ.erase (1 : (H0 ⧸ M) →* ℂˣ)).card : ℂ)) * z := by
  classical
  -- The summand is constant across the erased finite dual, so the sum is cardinal times `z`.
  simp [nsmul_eq_mul]

/-- Helper for Remark 11-11.1-3: before collapsing the direct quotient-difference family, the
linearized exact slice together with the strict slice is exactly the full nontrivial nonfaithful
smaller-kernel sum. This isolates the already-settled reindexing algebra from the remaining
source-faithful owner partition. -/
theorem strict_branch_linearized_exact_slice_plus_strict_slice_eq_total_smaller_sum
    {H0 : Type} [Group H0] [Finite H0]
    (δ : H0 →* ℂˣ)
    (M : Subgroup H0) [M.Normal]
    (hδker_lt_M : δ.ker < M)
    (hprime : (Nat.card (H0 ⧸ M)).Prime)
    (ξH : R(H0)) :
    let δq : (H0 ⧸ δ.ker) →* ℂˣ :=
      QuotientGroup.lift δ.ker δ (show δ.ker ≤ δ.ker from le_rfl)
    let exactSlice : Finset ((H0 ⧸ δ.ker) →* ℂˣ) :=
      ((((Finset.univ.erase δq).filter fun γ => γ.ker ≠ ⊥).erase 1).filter
        fun γ => γ.ker = M.map (QuotientGroup.mk' δ.ker))
    let strictSlice : Finset ((H0 ⧸ δ.ker) →* ℂˣ) :=
      ((((Finset.univ.erase δq).filter fun γ => γ.ker ≠ ⊥).erase 1).filter
        fun γ => γ.ker ≠ M.map (QuotientGroup.mk' δ.ker))
    let smallerTop : ((H0 ⧸ δ.ker) →* ℂˣ) → ℂ := fun γ ↦
      let ε : H0 →* ℂˣ := γ.comp (QuotientGroup.mk' δ.ker)
      let ηε : R(H0 ⧸ ε.ker) :=
        (ε.ker.index : ℤ) • (1 : R(H0 ⧸ ε.ker)) +
          Finset.sum
            (((Finset.univ.erase
                (QuotientGroup.lift ε.ker ε (show ε.ker ≤ ε.ker from le_rfl))).filter
              fun θ => θ.ker = ⊥))
            (fun θ ↦ ((θ.toCharacterRing - 1 : R(H0 ⧸ ε.ker))))
      quotient_pullback_pairing_linearMap ε ξH ηε
    let P : ℂ :=
      ⟪(Subgroup.characterRingInduction M (1 : R(M)) : H0 → ℂ), (ξH : H0 → ℂ)⟫
    let directDiff : ((H0 ⧸ M) →* ℂˣ) → ℂ := fun β ↦
      ⟪(((β.comp (QuotientGroup.mk' M)).toCharacterRing - 1 : R(H0)) : H0 → ℂ),
          (ξH : H0 → ℂ)⟫
    ((∑ _β ∈ Finset.univ.erase (1 : (H0 ⧸ M) →* ℂˣ), P) -
        ∑ β ∈ Finset.univ.erase (1 : (H0 ⧸ M) →* ℂˣ), directDiff β) +
        ∑ γ ∈ strictSlice, smallerTop γ =
      ∑ γ ∈ (((Finset.univ.erase δq).filter fun γ => γ.ker ≠ ⊥).erase 1), smallerTop γ := by
  classical
  let δq : (H0 ⧸ δ.ker) →* ℂˣ :=
    QuotientGroup.lift δ.ker δ (show δ.ker ≤ δ.ker from le_rfl)
  let exactSlice : Finset ((H0 ⧸ δ.ker) →* ℂˣ) :=
    ((((Finset.univ.erase δq).filter fun γ => γ.ker ≠ ⊥).erase 1).filter
      fun γ => γ.ker = M.map (QuotientGroup.mk' δ.ker))
  let strictSlice : Finset ((H0 ⧸ δ.ker) →* ℂˣ) :=
    ((((Finset.univ.erase δq).filter fun γ => γ.ker ≠ ⊥).erase 1).filter
      fun γ => γ.ker ≠ M.map (QuotientGroup.mk' δ.ker))
  let smallerTop : ((H0 ⧸ δ.ker) →* ℂˣ) → ℂ := fun γ ↦
    let ε : H0 →* ℂˣ := γ.comp (QuotientGroup.mk' δ.ker)
    let ηε : R(H0 ⧸ ε.ker) :=
      (ε.ker.index : ℤ) • (1 : R(H0 ⧸ ε.ker)) +
        ∑ θ ∈
            ((Finset.univ.erase
                (QuotientGroup.lift ε.ker ε (show ε.ker ≤ ε.ker from le_rfl))).filter
              fun θ => θ.ker = ⊥),
            ((θ.toCharacterRing - 1 : R(H0 ⧸ ε.ker)))
    quotient_pullback_pairing_linearMap ε ξH ηε
  let P : ℂ :=
    ⟪(Subgroup.characterRingInduction M (1 : R(M)) : H0 → ℂ), (ξH : H0 → ℂ)⟫
  let directDiff : ((H0 ⧸ M) →* ℂˣ) → ℂ := fun β ↦
    ⟪(((β.comp (QuotientGroup.mk' M)).toCharacterRing - 1 : R(H0)) : H0 → ℂ),
        (ξH : H0 → ℂ)⟫
  have hslice_partition :
      ∑ γ ∈ (((Finset.univ.erase δq).filter fun γ => γ.ker ≠ ⊥).erase 1), smallerTop γ =
        ∑ γ ∈ exactSlice, smallerTop γ + ∑ γ ∈ strictSlice, smallerTop γ := by
    -- First split the nontrivial nonfaithful branch into the exact mapped-coatom slice and its
    -- strict complement.
    exact
      strict_branch_nontrivial_nonfaithful_smaller_top_layer_partition_by_mapped_coatom
        (δ := δ)
        (M := M)
        (ξH := ξH)
  have hexact_sum_reindex :
      ∑ γ ∈ exactSlice, smallerTop γ =
        ∑ β ∈ Finset.univ.erase (1 : (H0 ⧸ M) →* ℂˣ),
          smallerTop
            (((β.comp
                (QuotientGroup.quotientQuotientEquivQuotient δ.ker M hδker_lt_M.le).toMonoidHom).comp
                (QuotientGroup.mk' (M.map (QuotientGroup.mk' δ.ker)))) :
              (H0 ⧸ δ.ker) →* ℂˣ) := by
    -- Reindex the exact slice by the nontrivial direct quotient characters.
    exact
      strict_branch_exact_slice_sum_reindex
        (δ := δ)
        (M := M)
        hδker_lt_M
        hprime
        smallerTop
  have hexact_sum_reindexed_termwise :
      ∑ β ∈ Finset.univ.erase (1 : (H0 ⧸ M) →* ℂˣ),
          smallerTop
            (((β.comp
                (QuotientGroup.quotientQuotientEquivQuotient δ.ker M hδker_lt_M.le).toMonoidHom).comp
                (QuotientGroup.mk' (M.map (QuotientGroup.mk' δ.ker)))) :
              (H0 ⧸ δ.ker) →* ℂˣ) =
        ∑ β ∈ Finset.univ.erase (1 : (H0 ⧸ M) →* ℂˣ), (P - directDiff β) := by
    -- Then rewrite each reindexed exact-slice term into the coatom pairing minus the transported
    -- direct quotient difference term.
    refine Finset.sum_congr rfl ?_
    intro β hβ
    exact
      strict_branch_reindexed_exact_slice_term_eq_coatom_pairing_minus_direct_difference
        (δ := δ)
        (M := M)
        hδker_lt_M
        hprime
        (ξH := ξH)
        (β := β)
        hβ
  have hexact_sum_reindexed_linearized :
      ∑ γ ∈ exactSlice, smallerTop γ =
        (∑ _β ∈ Finset.univ.erase (1 : (H0 ⧸ M) →* ℂˣ), P) -
          ∑ β ∈ Finset.univ.erase (1 : (H0 ⧸ M) →* ℂˣ), directDiff β := by
    -- The finite sum algebra is now isolated from the source-level owner partition.
    rw [hexact_sum_reindex, hexact_sum_reindexed_termwise, Finset.sum_sub_distrib]
  -- Replace the exact slice by its linearized direct-quotient package, then merge it back with
  -- the strict slice to recover the full smaller-kernel branch.
  calc
    ((∑ _β ∈ Finset.univ.erase (1 : (H0 ⧸ M) →* ℂˣ), P) -
          ∑ β ∈ Finset.univ.erase (1 : (H0 ⧸ M) →* ℂˣ), directDiff β) +
        ∑ γ ∈ strictSlice, smallerTop γ =
      (∑ γ ∈ exactSlice, smallerTop γ) + ∑ γ ∈ strictSlice, smallerTop γ := by
        rw [← hexact_sum_reindexed_linearized]
    _ =
      ∑ γ ∈ (((Finset.univ.erase δq).filter fun γ => γ.ker ≠ ⊥).erase 1), smallerTop γ := by
        simpa [add_assoc, add_left_comm, add_comm] using hslice_partition.symm

/-- Helper for Remark 11-11.1-3: in the strict branch, the full nonfaithful residual family is
the exceptional trivial branch plus the full smaller-kernel top-layer package. This isolates the
only easy normalization needed before the source-facing owner partition. -/
theorem strict_branch_nonfaithful_residual_sum_eq_trivial_plus_smaller_top
    {H0 : Type} [Group H0] [Finite H0]
    (δ : H0 →* ℂˣ)
    (M : Subgroup H0) [M.Normal]
    (hδker_lt_M : δ.ker < M)
    (ξH : R(H0)) :
    let δq : (H0 ⧸ δ.ker) →* ℂˣ :=
      QuotientGroup.lift δ.ker δ (show δ.ker ≤ δ.ker from le_rfl)
    let residualTerm : ((H0 ⧸ δ.ker) →* ℂˣ) → ℂ := fun γ ↦
      let ε : H0 →* ℂˣ := γ.comp (QuotientGroup.mk' δ.ker)
      (ε.ker.index : ℂ) * ⟪((1 : R(H0)) : H0 → ℂ), (ξH : H0 → ℂ)⟫ +
        ∑ θ ∈
            ((Finset.univ.erase
                (QuotientGroup.lift ε.ker ε (show ε.ker ≤ ε.ker from le_rfl))).filter
              fun θ => θ.ker = ⊥),
            ⟪(((θ.comp (QuotientGroup.mk' ε.ker)).toCharacterRing - 1 : R(H0)) :
                  H0 → ℂ),
                (ξH : H0 → ℂ)⟫
    ∑ γ ∈ ((Finset.univ.erase δq).filter fun γ => γ.ker ≠ ⊥), residualTerm γ =
      quotient_pullback_pairing_linearMap δ ξH (1 : R(H0 ⧸ δ.ker)) +
        ∑ γ ∈ (((Finset.univ.erase δq).filter fun γ => γ.ker ≠ ⊥).erase 1),
          let ε : H0 →* ℂˣ := γ.comp (QuotientGroup.mk' δ.ker)
          let ηε : R(H0 ⧸ ε.ker) :=
            (ε.ker.index : ℤ) • (1 : R(H0 ⧸ ε.ker)) +
              ∑ θ ∈
                  ((Finset.univ.erase
                      (QuotientGroup.lift ε.ker ε (show ε.ker ≤ ε.ker from le_rfl))).filter
                    fun θ => θ.ker = ⊥),
                  ((θ.toCharacterRing - 1 : R(H0 ⧸ ε.ker)))
          quotient_pullback_pairing_linearMap ε ξH ηε := by
  classical
  dsimp
  let residualTerm : ((H0 ⧸ δ.ker) →* ℂˣ) → ℂ := fun γ ↦
    let ε : H0 →* ℂˣ := γ.comp (QuotientGroup.mk' δ.ker)
    (ε.ker.index : ℂ) * ⟪((1 : R(H0)) : H0 → ℂ), (ξH : H0 → ℂ)⟫ +
      ∑ θ ∈
          ((Finset.univ.erase
              (QuotientGroup.lift ε.ker ε (show ε.ker ≤ ε.ker from le_rfl))).filter
            fun θ => θ.ker = ⊥),
          ⟪(((θ.comp (QuotientGroup.mk' ε.ker)).toCharacterRing - 1 : R(H0)) :
                H0 → ℂ),
              (ξH : H0 → ℂ)⟫
  set qpp1 : ℂ := quotient_pullback_pairing_linearMap δ ξH (1 : R(H0 ⧸ δ.ker))
  set smallerTop : ((H0 ⧸ δ.ker) →* ℂˣ) → ℂ := fun γ ↦
    let ε : H0 →* ℂˣ := γ.comp (QuotientGroup.mk' δ.ker)
    let ηε : R(H0 ⧸ ε.ker) :=
      (ε.ker.index : ℤ) • (1 : R(H0 ⧸ ε.ker)) +
        ∑ θ ∈
            ((Finset.univ.erase
                (QuotientGroup.lift ε.ker ε (show ε.ker ≤ ε.ker from le_rfl))).filter
              fun θ => θ.ker = ⊥),
            ((θ.toCharacterRing - 1 : R(H0 ⧸ ε.ker)))
    quotient_pullback_pairing_linearMap ε ξH ηε
  have hδ : δ ≠ 1 := by
    -- The strict branch excludes the trivial ambient character because `δ.ker < M`.
    intro hδ
    have hker_top : δ.ker = ⊤ := by
      ext x
      simp [hδ, MonoidHom.mem_ker]
    have hnot_lt : ¬ δ.ker < M := by
      simpa [hker_top] using (show ¬ (⊤ : Subgroup H0) < M from not_lt_of_ge le_top)
    exact hnot_lt hδker_lt_M
  have hsplit :
      ∑ γ ∈
          ((Finset.univ.erase
              (QuotientGroup.lift δ.ker δ (show δ.ker ≤ δ.ker from le_rfl))).filter
            fun γ => γ.ker ≠ ⊥),
          residualTerm γ =
        residualTerm (1 : (H0 ⧸ δ.ker) →* ℂˣ) +
          ∑ γ ∈
              (((Finset.univ.erase
                  (QuotientGroup.lift δ.ker δ (show δ.ker ≤ δ.ker from le_rfl))).filter
                fun γ => γ.ker ≠ ⊥).erase 1),
              residualTerm γ := by
    -- Split off the exceptional trivial branch before rewriting the genuine smaller-kernel terms.
    simpa [residualTerm] using
      strict_branch_nonfaithful_residual_sum_split_at_one
        (δ := δ)
        (ξH := ξH)
        hδ
  have htrivial :
      residualTerm (1 : (H0 ⧸ δ.ker) →* ℂˣ) = qpp1 := by
    -- The exceptional branch is exactly the trivial quotient-character pullback pairing.
    simpa [qpp1, residualTerm] using
      strict_branch_trivial_nonfaithful_erased_branch_identity
        (δ := δ)
        (ξH := ξH)
  have hnontrivial :
      ∑ γ ∈
          (((Finset.univ.erase
              (QuotientGroup.lift δ.ker δ (show δ.ker ≤ δ.ker from le_rfl))).filter
            fun γ => γ.ker ≠ ⊥).erase 1),
          residualTerm γ =
        ∑ γ ∈
            (((Finset.univ.erase
                (QuotientGroup.lift δ.ker δ (show δ.ker ≤ δ.ker from le_rfl))).filter
              fun γ => γ.ker ≠ ⊥).erase 1),
            smallerTop γ := by
    -- Every remaining nonfaithful summand is already the faithful top layer for a smaller kernel.
    exact
      strict_branch_nontrivial_nonfaithful_residual_sum_as_smaller_top_layers
        (δ := δ)
        (ξH := ξH)
  -- Normalize the full residual family by first splitting off `γ = 1` and then rewriting the
  -- genuine nontrivial branch termwise.
  exact Eq.trans (by exact hsplit) (by rw [htrivial, hnontrivial])


end CharacterizationOfCharacters

end Representation
