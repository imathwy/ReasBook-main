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

noncomputable section

universe v

namespace Representation

section CharacterizationOfCharacters

open scoped Pointwise Representation SubgroupInduction TensorProduct

variable {G : Type} [Group G] [Finite G]
variable {A : Type v} [CommRing A]

local notation:max s " •ᶜ " H => (MulAut.conj s • H : Subgroup G)

/-- Helper for Remark 11-11.1-3: every subgroup of a finite group is finite. -/
local instance fintypeHelperLocalMappedCoatomSlices1 (H : Subgroup G) : Fintype H := Fintype.ofFinite H

/-- Helper for Remark 11-11.1-3: the degree-one characters of a finite group form a finite type. -/
noncomputable local instance fintypeHelperLocalMappedCoatomSlicesA
    (Q : Type*) [Group Q] [Finite Q] : Fintype (Q →* ℂˣ) := Fintype.ofFinite _

/-- Helper for Remark 11-11.1-3: quotients of finite groups are finite types. -/
noncomputable local instance fintypeHelperLocalMappedCoatomSlicesB
    (Q : Type*) [Group Q] [Finite Q] (M : Subgroup Q) : Fintype (Q ⧸ M) :=
  Fintype.ofFinite _

/-- Helper for Remark 11-11.1-3: one canonical classical decidable equality for characters. -/
noncomputable local instance (priority := 2000) fintypeHelperLocalMappedCoatomSlicesC
    (Q : Type*) [Group Q] : DecidableEq (Q →* ℂˣ) := Classical.decEq _

attribute [local instance] Classical.propDecidable
/-- Helper for Remark 11-11.1-3: once the exceptional term `γ = 1` is separated, the whole
nonfaithful erased quotient branch is the trivial quotient-character contribution plus one
packaged `n`-multiple. -/
theorem strict_branch_full_nonfaithful_residual_sum_eq_trivial_plus_divisible
    {H0 : Type} [Group H0] [Finite H0] {n : ℤ}
    (δ : H0 →* ℂˣ)
    (M : Subgroup H0) [M.Normal]
    (hδker_lt_M : δ.ker < M)
    (ξH : R(H0))
    (hsmaller :
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
              algebraMap ℤ ℂ (n * bC)) :
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
    ∃ bNF : ℤ,
      ∑ γ ∈ ((Finset.univ.erase δq).filter fun γ => γ.ker ≠ ⊥), residualTerm γ =
        quotient_pullback_pairing_linearMap δ ξH (1 : R(H0 ⧸ δ.ker)) +
          algebraMap ℤ ℂ (n * bNF) := by
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
  have hδ : δ ≠ 1 := by
    intro hδ
    have hker_top : δ.ker = ⊤ := by
      ext x
      simp [hδ, MonoidHom.mem_ker]
    have hnot_lt : ¬ δ.ker < M := by
      simpa [hker_top] using (show ¬ (⊤ : Subgroup H0) < M from not_lt_of_ge le_top)
    exact hnot_lt hδker_lt_M
  have hsplit :
      ∑ γ ∈ ((Finset.univ.erase
          (QuotientGroup.lift δ.ker δ (show δ.ker ≤ δ.ker from le_rfl))).filter
        fun γ => γ.ker ≠ ⊥),
          residualTerm γ =
        residualTerm (1 : (H0 ⧸ δ.ker) →* ℂˣ) +
          ∑ γ ∈
              (((Finset.univ.erase
                  (QuotientGroup.lift δ.ker δ (show δ.ker ≤ δ.ker from le_rfl))).filter
                fun γ => γ.ker ≠ ⊥).erase 1),
              residualTerm γ := by
    -- Separate the exceptional erased nonfaithful branch before applying the packaged
    -- smaller-kernel arithmetic.
    exact
      strict_branch_nonfaithful_residual_sum_split_at_one
        (δ := δ)
        (ξH := ξH)
        hδ
  have htrivial :
      residualTerm (1 : (H0 ⧸ δ.ker) →* ℂˣ) =
        quotient_pullback_pairing_linearMap δ ξH (1 : R(H0 ⧸ δ.ker)) := by
    -- The exceptional branch is exactly the trivial quotient-character contribution.
    exact
      strict_branch_trivial_nonfaithful_erased_branch_identity
        (δ := δ)
        (ξH := ξH)
  have hnontrivial :
      ∃ bNF : ℤ,
        ∑ γ ∈
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
    ∑ γ ∈ ((Finset.univ.erase
        (QuotientGroup.lift δ.ker δ (show δ.ker ≤ δ.ker from le_rfl))).filter
      fun γ => γ.ker ≠ ⊥),
        residualTerm γ =
      residualTerm (1 : (H0 ⧸ δ.ker) →* ℂˣ) +
        ∑ γ ∈
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
theorem strict_branch_full_nonfaithful_residual_minus_trivial_divisible
    {H0 : Type} [Group H0] [Finite H0] {n : ℤ}
    (δ : H0 →* ℂˣ)
    (M : Subgroup H0) [M.Normal]
    (hδker_lt_M : δ.ker < M)
    (ξH : R(H0))
    (hsmaller :
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
              algebraMap ℤ ℂ (n * bC)) :
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
    ∃ bNF : ℤ,
      (∑ γ ∈ ((Finset.univ.erase δq).filter fun γ => γ.ker ≠ ⊥), residualTerm γ) -
          quotient_pullback_pairing_linearMap δ ξH (1 : R(H0 ⧸ δ.ker)) =
        algebraMap ℤ ℂ (n * bNF) := by
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
    (∑ γ ∈ ((Finset.univ.erase
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
theorem strict_branch_nonfaithful_residual_term_as_smaller_top_layer
    {H0 : Type} [Group H0] [Finite H0]
    (δ : H0 →* ℂˣ)
    (ξH : R(H0))
    (γ : (H0 ⧸ δ.ker) →* ℂˣ) :
    let ε : H0 →* ℂˣ := γ.comp (QuotientGroup.mk' δ.ker)
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
    let ηε : R(H0 ⧸ ε.ker) :=
      (ε.ker.index : ℤ) • (1 : R(H0 ⧸ ε.ker)) +
        ∑ θ ∈
            ((Finset.univ.erase
                (QuotientGroup.lift ε.ker ε (show ε.ker ≤ ε.ker from le_rfl))).filter
              fun θ => θ.ker = ⊥),
            ((θ.toCharacterRing - 1 : R(H0 ⧸ ε.ker)))
    residualTerm γ = quotient_pullback_pairing_linearMap ε ξH ηε := by
  classical
  dsimp
  let ε : H0 →* ℂˣ := γ.comp (QuotientGroup.mk' δ.ker)
  -- Rewrite the residual scalar directly as the smaller-kernel faithful top layer.
  simpa using faithful_quotient_top_layer_eq_quotient_pullback_pairing (β := ε) (ξ := ξH)

/-- Helper for Remark 11-11.1-3: after removing the exceptional `γ = 1` branch, the remaining
nonfaithful residual family is exactly the sum of the smaller-kernel faithful top-layer pairings.
-/
theorem strict_branch_nontrivial_nonfaithful_residual_sum_as_smaller_top_layers
    {H0 : Type} [Group H0] [Finite H0]
    (δ : H0 →* ℂˣ)
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
    ∑ γ ∈ (((Finset.univ.erase δq).filter fun γ => γ.ker ≠ ⊥).erase 1), residualTerm γ =
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
  refine Finset.sum_congr rfl ?_
  intro γ hγ
  -- Rewrite each nontrivial nonfaithful residual summand by the smaller-kernel top-layer
  -- package before attempting the global partition.
  simpa using
    strict_branch_nonfaithful_residual_term_as_smaller_top_layer
      (δ := δ)
      (ξH := ξH)
      γ

/-- Helper for Remark 11-11.1-3: the mapped-coatom correction term `ηM` already reduces to the
index-scaled trivial line after applying the quotient pullback pairing. -/
theorem strict_branch_etaM_pairing_eq_mapped_coatom_index_trivial
    {H0 : Type} [Group H0] [Finite H0]
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
    exact
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
          rw [map_sub, map_sum]
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
theorem strict_branch_iterated_difference_sum_eq_prime_quotient_faithful_sum
    {H0 : Type} [Group H0] [Finite H0]
    (δ : H0 →* ℂˣ)
    (M : Subgroup H0) [M.Normal]
    (hδker_lt_M : δ.ker < M)
    (hprime : (Nat.card (H0 ⧸ M)).Prime)
    (ξH : R(H0)) :
    let Mq : Subgroup (H0 ⧸ δ.ker) := M.map (QuotientGroup.mk' δ.ker)
    ∑ β : ((H0 ⧸ δ.ker) ⧸ Mq) →* ℂˣ,
      quotient_pullback_pairing_linearMap δ ξH
        (((β.comp (QuotientGroup.mk' Mq)).toCharacterRing - 1 : R(H0 ⧸ δ.ker))) =
      ∑ β ∈ ((Finset.univ.erase (1 : (H0 ⧸ M) →* ℂˣ)).filter fun β => β.ker = ⊥),
        ⟪(((β.comp (QuotientGroup.mk' M)).toCharacterRing - 1 : R(H0)) : H0 → ℂ),
            (ξH : H0 → ℂ)⟫ := by
  classical
  dsimp
  let e : ((H0 ⧸ δ.ker) ⧸ M.map (QuotientGroup.mk' δ.ker)) ≃* H0 ⧸ M :=
    QuotientGroup.quotientQuotientEquivQuotient δ.ker M hδker_lt_M.le
  let eχ :
      ((H0 ⧸ M) →* ℂˣ) ≃
        (((H0 ⧸ δ.ker) ⧸ M.map (QuotientGroup.mk' δ.ker)) →* ℂˣ) :=
    { toFun := fun β ↦ β.comp e.toMonoidHom
      invFun := fun β ↦ β.comp e.symm.toMonoidHom
      left_inv := by
        intro β
        refine MonoidHom.ext fun x ↦ ?_
        simp
      right_inv := by
        intro β
        refine MonoidHom.ext fun x ↦ ?_
        simp }
  let iterTerm :
      (((H0 ⧸ δ.ker) ⧸ M.map (QuotientGroup.mk' δ.ker)) →* ℂˣ) → ℂ := fun β ↦
        quotient_pullback_pairing_linearMap δ ξH
          (((β.comp (QuotientGroup.mk' (M.map (QuotientGroup.mk' δ.ker)))).toCharacterRing - 1 :
              R(H0 ⧸ δ.ker)))
  let directTerm : ((H0 ⧸ M) →* ℂˣ) → ℂ := fun β ↦
    ⟪(((β.comp (QuotientGroup.mk' M)).toCharacterRing - 1 : R(H0)) : H0 → ℂ),
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
    exact (Fintype.sum_equiv eχ directTerm iterTerm htransport).symm
  have hsplit :
      ∑ β : (H0 ⧸ M) →* ℂˣ, directTerm β =
        directTerm (1 : (H0 ⧸ M) →* ℂˣ) +
          ∑ β ∈ Finset.univ.erase (1 : (H0 ⧸ M) →* ℂˣ), directTerm β := by
    -- Isolate the trivial quotient character so the remaining family matches the faithful branch.
    simpa [directTerm] using
      (Finset.sum_erase_add
        (s := Finset.univ)
        (a := (1 : (H0 ⧸ M) →* ℂˣ))
        (by simp)).symm
  have hone :
      directTerm (1 : (H0 ⧸ M) →* ℂˣ) = 0 := by
    -- The trivial quotient character contributes the zero difference term.
    have hzero :
        (((1 : (H0 ⧸ M) →* ℂˣ).comp (QuotientGroup.mk' M)).toCharacterRing - 1 : R(H0)) = 0 := by
      rw [MonoidHom.one_comp]
      apply Subtype.ext
      ext h
      simp [MonoidHom.toCharacterRing_apply]
    simp [directTerm, hzero, Representation.groupFunctionPairingOverField]
  calc
    ∑ β : ((H0 ⧸ δ.ker) ⧸ M.map (QuotientGroup.mk' δ.ker)) →* ℂˣ, iterTerm β =
        ∑ β : (H0 ⧸ M) →* ℂˣ, directTerm β := hsum_transport
    _ =
        directTerm (1 : (H0 ⧸ M) →* ℂˣ) +
          ∑ β ∈ Finset.univ.erase (1 : (H0 ⧸ M) →* ℂˣ), directTerm β := hsplit
    _ =
        ∑ β ∈ Finset.univ.erase (1 : (H0 ⧸ M) →* ℂˣ), directTerm β := by
          rw [hone]
          simp
    _ =
        ∑ β ∈ ((Finset.univ.erase (1 : (H0 ⧸ M) →* ℂˣ)).filter fun β => β.ker = ⊥),
          directTerm β := by
            symm
            simpa [prime_quotient_faithful_filter_eq_erase_one (M := M) hprime]

/-- Helper for Remark 11-11.1-3: splitting an erased quotient-character family by kernel type
records the faithful and nonfaithful branches separately. -/
theorem strict_branch_erased_sum_split_by_kernel_type
    {Q : Type*} [Group Q] [Finite Q]
    (δq : Q →* ℂˣ)
    (ambientTerm : (Q →* ℂˣ) → ℂ) :
    ∑ γ ∈ Finset.univ.erase δq, ambientTerm γ =
      ∑ γ ∈ ((Finset.univ.erase δq).filter fun γ => γ.ker = ⊥), ambientTerm γ +
        ∑ γ ∈ ((Finset.univ.erase δq).filter fun γ => γ.ker ≠ ⊥), ambientTerm γ := by
  classical
  -- Split the erased quotient-character family once into faithful and nonfaithful branches.
  simpa using
    (Finset.sum_filter_add_sum_filter_not
      (s := Finset.univ.erase δq)
      (f := ambientTerm)
      (p := fun γ : Q →* ℂˣ => γ.ker = ⊥)).symm

/-- Helper for Remark 11-11.1-3: after removing the exceptional trivial branch, the remaining
nonfaithful quotient-character family splits into the chosen-coatom kernel stratum and its strict
complement. -/
theorem strict_branch_nontrivial_nonfaithful_sum_split_by_mapped_coatom_kernel
    {H0 : Type} [Group H0] [Finite H0]
    (δ : H0 →* ℂˣ)
    (M : Subgroup H0)
    (F : ((H0 ⧸ δ.ker) →* ℂˣ) → ℂ) :
    let δq : (H0 ⧸ δ.ker) →* ℂˣ :=
      QuotientGroup.lift δ.ker δ (show δ.ker ≤ δ.ker from le_rfl)
    let S : Finset ((H0 ⧸ δ.ker) →* ℂˣ) :=
      (((Finset.univ.erase δq).filter fun γ => γ.ker ≠ ⊥).erase 1)
    ∑ γ ∈ S, F γ =
      ∑ γ ∈ S.filter (fun γ => γ.ker = M.map (QuotientGroup.mk' δ.ker)), F γ +
        ∑ γ ∈ S.filter (fun γ => γ.ker ≠ M.map (QuotientGroup.mk' δ.ker)), F γ := by
  classical
  dsimp
  -- Make the chosen-coatom kernel stratum explicit before matching it with the transported
  -- prime-quotient branch.
  simpa using
    (Finset.sum_filter_add_sum_filter_not
      (s := ((((Finset.univ.erase
          (QuotientGroup.lift δ.ker δ (show δ.ker ≤ δ.ker from le_rfl))).filter
        fun γ => γ.ker ≠ ⊥).erase 1)))
      (f := F)
      (p := fun γ : (H0 ⧸ δ.ker) →* ℂˣ =>
        γ.ker = M.map (QuotientGroup.mk' δ.ker))).symm

/-- Helper for Remark 11-11.1-3: after removing the exceptional trivial branch, the remaining
smaller-kernel package splits exactly into the mapped-coatom kernel slice and its strict
complement. This is the stable source-faithful partition before any termwise expansion of the
exact-kernel slice. -/
theorem strict_branch_nontrivial_nonfaithful_smaller_top_layer_partition_by_mapped_coatom
    {H0 : Type} [Group H0] [Finite H0]
    (δ : H0 →* ℂˣ)
    (M : Subgroup H0) [M.Normal]
    (ξH : R(H0)) :
    let δq : (H0 ⧸ δ.ker) →* ℂˣ :=
      QuotientGroup.lift δ.ker δ (show δ.ker ≤ δ.ker from le_rfl)
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
    let S : Finset ((H0 ⧸ δ.ker) →* ℂˣ) :=
      (((Finset.univ.erase δq).filter fun γ => γ.ker ≠ ⊥).erase 1)
    ∑ γ ∈ S, smallerTop γ =
      ∑ γ ∈ S.filter (fun γ => γ.ker = M.map (QuotientGroup.mk' δ.ker)), smallerTop γ +
        ∑ γ ∈ S.filter (fun γ => γ.ker ≠ M.map (QuotientGroup.mk' δ.ker)), smallerTop γ := by
  classical
  dsimp
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
  let S : Finset ((H0 ⧸ δ.ker) →* ℂˣ) :=
    (((Finset.univ.erase
        (QuotientGroup.lift δ.ker δ (show δ.ker ≤ δ.ker from le_rfl))).filter
      fun γ => γ.ker ≠ ⊥).erase 1)
  have hsplit_kernel :
      ∑ γ ∈ S, smallerTop γ =
        ∑ γ ∈ S.filter (fun γ => γ.ker = M.map (QuotientGroup.mk' δ.ker)), smallerTop γ +
          ∑ γ ∈ S.filter (fun γ => γ.ker ≠ M.map (QuotientGroup.mk' δ.ker)), smallerTop γ := by
    -- Split the erased nonfaithful family at the chosen coatom before identifying each stratum.
    exact
      strict_branch_nontrivial_nonfaithful_sum_split_by_mapped_coatom_kernel
        (δ := δ)
        (M := M)
        (F := smallerTop)
  -- Route correction: the earlier scaffold tried to collapse the exact-kernel slice at this stage,
  -- but the stable source route only provides the raw kernel partition here.
  exact hsplit_kernel

/-- Helper for Remark 11-11.1-3: a strict-slice member is already a genuine smaller-kernel
branch. It is nontrivial, remains nonfaithful on the kernel quotient, and its ambient pullback
has strictly smaller kernel index than `δ`. -/
theorem strict_branch_strict_slice_member_data
    {H0 : Type} [Group H0] [Finite H0]
    (δ : H0 →* ℂˣ)
    (M : Subgroup H0)
    {γ : (H0 ⧸ δ.ker) →* ℂˣ}
    (hγ :
      γ ∈ ((((Finset.univ.erase
          (QuotientGroup.lift δ.ker δ (show δ.ker ≤ δ.ker from le_rfl))).filter
        fun γ => γ.ker ≠ ⊥).erase 1).filter
        fun γ => γ.ker ≠ M.map (QuotientGroup.mk' δ.ker))) :
    γ ≠ 1 ∧
      γ.ker ≠ ⊥ ∧
      (γ.comp (QuotientGroup.mk' δ.ker)) ≠ 1 ∧
      (γ.comp (QuotientGroup.mk' δ.ker)).ker.index < δ.ker.index := by
  let δq : (H0 ⧸ δ.ker) →* ℂˣ :=
    QuotientGroup.lift δ.ker δ (show δ.ker ≤ δ.ker from le_rfl)
  have hγ_mem :
      γ ∈ (((Finset.univ.erase δq).filter fun γ => γ.ker ≠ ⊥).erase 1) := by
    -- Forget the final strict-kernel filter to recover the underlying erased nonfaithful branch.
    exact (Finset.mem_filter.mp hγ).1
  have hγ_ne : γ ≠ 1 := by
    -- Membership in the erased branch already excludes the exceptional trivial quotient character.
    exact (Finset.mem_erase.mp hγ_mem).1
  have hγ_nonfaithful :
      γ ∈ ((Finset.univ.erase δq).filter fun γ => γ.ker ≠ ⊥) := by
    -- The erased branch still records that `γ` is nonfaithful on the quotient.
    exact (Finset.mem_erase.mp hγ_mem).2
  have hγker_ne : γ.ker ≠ ⊥ := by
    -- The remaining filter condition is exactly the nontrivial-kernel hypothesis needed below.
    exact (Finset.mem_filter.mp hγ_nonfaithful).2
  have hε_ne : (γ.comp (QuotientGroup.mk' δ.ker)) ≠ 1 := by
    -- If the ambient pullback were trivial, surjectivity of `mk'` would force `γ = 1`.
    intro hε
    apply hγ_ne
    refine MonoidHom.ext fun x ↦ ?_
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective δ.ker x
    simpa using DFunLike.congr_fun hε y
  have hε_lt :
      (γ.comp (QuotientGroup.mk' δ.ker)).ker.index < δ.ker.index := by
    -- A nonfaithful erased quotient character strictly enlarges the ambient kernel.
    simpa using
      kernel_growth_measure_decreases_on_nonfaithful_erased_branch δ γ hγker_ne
  exact ⟨hγ_ne, hγker_ne, hε_ne, hε_lt⟩

/-- Helper for Remark 11-11.1-3: membership in the exact mapped-coatom slice already packages the
transport facts needed for the later slice expansion. The slice excludes the trivial quotient
character, and pulling a slice member back along `mk' δ.ker` recovers the chosen coatom `M` as
its ambient kernel. -/
theorem strict_branch_exact_mapped_coatom_slice_member_data
    {H0 : Type} [Group H0] [Finite H0]
    (δ : H0 →* ℂˣ)
    (M : Subgroup H0) [M.Normal]
    (hδker_lt_M : δ.ker < M)
    {γ : (H0 ⧸ δ.ker) →* ℂˣ}
    (hγ :
      γ ∈ ((((Finset.univ.erase
          (QuotientGroup.lift δ.ker δ (show δ.ker ≤ δ.ker from le_rfl))).filter
        fun γ => γ.ker ≠ ⊥).erase 1).filter
        fun γ => γ.ker = M.map (QuotientGroup.mk' δ.ker))) :
    γ ≠ 1 ∧ (γ.comp (QuotientGroup.mk' δ.ker)).ker = M := by
  have hγ_mem :
      γ ∈ (((Finset.univ.erase
          (QuotientGroup.lift δ.ker δ (show δ.ker ≤ δ.ker from le_rfl))).filter
        fun γ => γ.ker ≠ ⊥).erase 1) := by
    -- Forget the final exact-kernel filter to recover the underlying erased nontrivial branch.
    exact (Finset.mem_filter.mp hγ).1
  have hγ_ne : γ ≠ 1 := by
    -- Membership in the erased branch already excludes the exceptional trivial quotient character.
    exact (Finset.mem_erase.mp hγ_mem).1
  have hγker :
      γ.ker = M.map (QuotientGroup.mk' δ.ker) := by
    -- The remaining filter records the exact mapped-coatom kernel condition.
    exact (Finset.mem_filter.mp hγ).2
  refine ⟨hγ_ne, ?_⟩
  -- Pull the exact slice kernel back along `mk' δ.ker` and collapse the transport to `M`.
  rw [← MonoidHom.comap_ker, hγker, quotient_comap_map_eq_of_le δ.ker M hδker_lt_M.le]

/-- Helper for Remark 11-11.1-3: every exact mapped-coatom slice member comes from a unique
nontrivial character of the direct quotient `H0 ⧸ M` after transporting across Noether's third
isomorphism and pulling back along the quotient map by `M.map (mk' δ.ker)`. -/
theorem strict_branch_exact_slice_member_eq_lifted_quotient_character
    {H0 : Type} [Group H0] [Finite H0]
    (δ : H0 →* ℂˣ)
    (M : Subgroup H0) [M.Normal]
    (hδker_lt_M : δ.ker < M)
    {γ : (H0 ⧸ δ.ker) →* ℂˣ}
    (hγ :
      γ ∈ ((((Finset.univ.erase
          (QuotientGroup.lift δ.ker δ (show δ.ker ≤ δ.ker from le_rfl))).filter
        fun γ => γ.ker ≠ ⊥).erase 1).filter
        fun γ => γ.ker = M.map (QuotientGroup.mk' δ.ker))) :
    ∃ β : (H0 ⧸ M) →* ℂˣ,
      β ≠ 1 ∧
        γ =
          (((β.comp
              (QuotientGroup.quotientQuotientEquivQuotient δ.ker M hδker_lt_M.le).toMonoidHom).comp
              (QuotientGroup.mk' (M.map (QuotientGroup.mk' δ.ker)))) : (H0 ⧸ δ.ker) →* ℂˣ) := by
  let Mq : Subgroup (H0 ⧸ δ.ker) := M.map (QuotientGroup.mk' δ.ker)
  let e : ((H0 ⧸ δ.ker) ⧸ Mq) ≃* H0 ⧸ M :=
    QuotientGroup.quotientQuotientEquivQuotient δ.ker M hδker_lt_M.le
  have hγ_ne : γ ≠ 1 := by
    -- Exact-slice membership already excludes the exceptional trivial quotient character.
    exact
      (strict_branch_exact_mapped_coatom_slice_member_data
        (δ := δ)
        (M := M)
        hδker_lt_M
        hγ).1
  have hγker : γ.ker = Mq := by
    -- The final filter in the exact slice records the mapped-coatom kernel condition.
    exact (Finset.mem_filter.mp hγ).2
  let γbar : ((H0 ⧸ δ.ker) ⧸ Mq) →* ℂˣ := QuotientGroup.lift Mq γ hγker.ge
  let β : (H0 ⧸ M) →* ℂˣ := γbar.comp e.symm.toMonoidHom
  have hβ_ne : β ≠ 1 := by
    intro hβ
    have hγbar_one : γbar = 1 := by
      refine MonoidHom.ext fun x ↦ ?_
      obtain ⟨y, rfl⟩ := e.symm.surjective x
      -- Transport the direct quotient equality back through `e` to recover the iterated lift.
      simpa [β] using DFunLike.congr_fun hβ y
    apply hγ_ne
    refine MonoidHom.ext fun x ↦ ?_
    -- Precomposing the iterated lift with the quotient map by `Mq` recovers the original slice
    -- member, so triviality of the lift would force triviality of `γ`.
    calc
      γ x = γbar (QuotientGroup.mk' Mq x) := by
        simpa [γbar] using congrFun (QuotientGroup.lift_comp_mk' Mq γ hγker.ge).symm x
      _ = 1 := by
        rw [hγbar_one]
        simp
  refine ⟨β, hβ_ne, ?_⟩
  refine MonoidHom.ext fun x ↦ ?_
  -- Rewrite `γ` through its iterated quotient lift and then transport that lift back across the
  -- third-isomorphism equivalence to the direct quotient character `β`.
  calc
    γ x = γbar (QuotientGroup.mk' Mq x) := by
      simpa [γbar] using congrFun (QuotientGroup.lift_comp_mk' Mq γ hγker.ge).symm x
    _ = ((β.comp e.toMonoidHom) (QuotientGroup.mk' Mq x)) := by
      simp [β]
    _ =
        (((β.comp
            (QuotientGroup.quotientQuotientEquivQuotient δ.ker M hδker_lt_M.le).toMonoidHom).comp
            (QuotientGroup.mk' (M.map (QuotientGroup.mk' δ.ker)))) x) := by
              simp [Mq, e]

/-- Helper for Remark 11-11.1-3: every nontrivial character of the prime quotient `H0 ⧸ M`
lifts to a member of the exact mapped-coatom slice after transporting through Noether's third
isomorphism and pulling back along the quotient by `M.map (mk' δ.ker)`. -/
theorem strict_branch_lifted_quotient_character_mem_exact_slice
    {H0 : Type} [Group H0] [Finite H0]
    (δ : H0 →* ℂˣ)
    (M : Subgroup H0) [M.Normal]
    (hδker_lt_M : δ.ker < M)
    (hprime : (Nat.card (H0 ⧸ M)).Prime)
    (β : (H0 ⧸ M) →* ℂˣ)
    (hβ : β ≠ 1) :
    let δq : (H0 ⧸ δ.ker) →* ℂˣ :=
      QuotientGroup.lift δ.ker δ (show δ.ker ≤ δ.ker from le_rfl)
    let Mq : Subgroup (H0 ⧸ δ.ker) := M.map (QuotientGroup.mk' δ.ker)
    let e : ((H0 ⧸ δ.ker) ⧸ Mq) ≃* H0 ⧸ M :=
      QuotientGroup.quotientQuotientEquivQuotient δ.ker M hδker_lt_M.le
    let γ : (H0 ⧸ δ.ker) →* ℂˣ :=
      (((β.comp e.toMonoidHom).comp (QuotientGroup.mk' Mq)) : (H0 ⧸ δ.ker) →* ℂˣ)
    γ ∈ ((((Finset.univ.erase δq).filter fun γ => γ.ker ≠ ⊥).erase 1).filter
      fun γ => γ.ker = Mq) := by
  classical
  let δq : (H0 ⧸ δ.ker) →* ℂˣ :=
    QuotientGroup.lift δ.ker δ (show δ.ker ≤ δ.ker from le_rfl)
  let Mq : Subgroup (H0 ⧸ δ.ker) := M.map (QuotientGroup.mk' δ.ker)
  let e : ((H0 ⧸ δ.ker) ⧸ Mq) ≃* H0 ⧸ M :=
    QuotientGroup.quotientQuotientEquivQuotient δ.ker M hδker_lt_M.le
  let γ : (H0 ⧸ δ.ker) →* ℂˣ :=
    (((β.comp e.toMonoidHom).comp (QuotientGroup.mk' Mq)) : (H0 ⧸ δ.ker) →* ℂˣ)
  let βiter : ((H0 ⧸ δ.ker) ⧸ Mq) →* ℂˣ := β.comp e.toMonoidHom
  have hβiter_ne : βiter ≠ 1 := by
    intro hβiter
    apply hβ
    refine MonoidHom.ext fun x ↦ ?_
    obtain ⟨y, rfl⟩ := e.surjective x
    -- Evaluate the transported equality on an `e`-preimage to recover the direct quotient
    -- character `β`.
    simpa [βiter] using DFunLike.congr_fun hβiter y
  have hprime_iter :
      (Nat.card (((H0 ⧸ δ.ker) ⧸ Mq))).Prime := by
    -- The iterated quotient has the same cardinality as the direct prime quotient `H0 ⧸ M`.
    simpa [Mq] using
      quotient_map_prime_card_of_prime_quotient
        δ.ker
        M
        hδker_lt_M.le
        hprime
  have hγker : γ.ker = Mq := by
    -- After transport to the iterated quotient, the lifted nontrivial character has exact kernel
    -- `Mq` by the prime-quotient kernel computation.
    simpa [γ, βiter] using
      lifted_prime_quotient_character_kernel_eq_coatom
        (H0 := H0 ⧸ δ.ker)
        (M := Mq)
        hprime_iter
        βiter
        hβiter_ne
  have hγ_ne_one : γ ≠ 1 := by
    intro hγ
    apply hβiter_ne
    refine MonoidHom.ext fun x ↦ ?_
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective Mq x
    -- Pull triviality back along the quotient map by `Mq` to recover triviality of the iterated
    -- quotient character.
    simpa [γ, βiter] using DFunLike.congr_fun hγ y
  have hγ_ne_δq : γ ≠ δq := by
    intro hγ_eq
    have hpull_ker :
        ((δq.comp (QuotientGroup.mk' δ.ker)) : H0 →* ℂˣ).ker = M := by
      -- If the lift coincided with `δq`, pulling kernels back to `H0` would identify `M` with
      -- `δ.ker`, contradicting the strict-branch assumption.
      calc
        ((δq.comp (QuotientGroup.mk' δ.ker)) : H0 →* ℂˣ).ker =
            ((γ.comp (QuotientGroup.mk' δ.ker)) : H0 →* ℂˣ).ker := by
              rw [hγ_eq]
        _ = M := by
              rw [← MonoidHom.comap_ker, hγker, quotient_comap_map_eq_of_le δ.ker M hδker_lt_M.le]
    have hδker_eq_M : δ.ker = M := by
      simpa [δq] using hpull_ker
    exact hδker_lt_M.ne hδker_eq_M
  have hMq_ne_bot : Mq ≠ ⊥ := by
    intro hMq_bot
    have hM_eq_ker : M = δ.ker := by
      calc
        M = Subgroup.comap (QuotientGroup.mk' δ.ker) Mq := by
              symm
              simpa [Mq] using quotient_comap_map_eq_of_le δ.ker M hδker_lt_M.le
        _ = δ.ker := by
              simp [Mq, hMq_bot]
    exact hδker_lt_M.ne hM_eq_ker.symm
  refine Finset.mem_filter.mpr ?_
  refine ⟨Finset.mem_erase.mpr ⟨hγ_ne_one, ?_⟩, hγker⟩
  refine Finset.mem_filter.mpr ⟨Finset.mem_erase.mpr ⟨hγ_ne_δq, by simp⟩, ?_⟩
  -- The exact-slice lift is genuinely nonfaithful because its kernel is the proper mapped
  -- coatom `Mq`.
  show ¬ γ.ker = ⊥
  rw [hγker]
  exact hMq_ne_bot


end CharacterizationOfCharacters

end Representation
