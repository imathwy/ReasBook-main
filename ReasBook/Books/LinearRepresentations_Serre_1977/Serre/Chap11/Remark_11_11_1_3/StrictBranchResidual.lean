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

noncomputable section

universe v

namespace Representation

section CharacterizationOfCharacters

open scoped Pointwise Representation SubgroupInduction TensorProduct

variable {G : Type} [Group G] [Finite G]
variable {A : Type v} [CommRing A]

local notation:max s " •ᶜ " H => (MulAut.conj s • H : Subgroup G)

/-- Helper for Remark 11-11.1-3: every subgroup of a finite group is finite. -/
local instance fintypeHelperLocalStrictBranchResidual1 (H : Subgroup G) : Fintype H := Fintype.ofFinite H

/-- Helper for Remark 11-11.1-3: the degree-one characters of a finite group form a finite type. -/
noncomputable local instance fintypeHelperLocalStrictBranchResidualA
    (Q : Type*) [Group Q] [Finite Q] : Fintype (Q →* ℂˣ) := Fintype.ofFinite _

/-- Helper for Remark 11-11.1-3: coset spaces of finite groups are finite types. -/
noncomputable local instance fintypeHelperLocalStrictBranchResidualB
    (Q : Type*) [Group Q] [Finite Q] (M : Subgroup Q) : Fintype (Q ⧸ M) :=
  Fintype.ofFinite _

/-- Helper for Remark 11-11.1-3: one canonical classical decidable equality for characters. -/
noncomputable local instance (priority := 2000) fintypeHelperLocalStrictBranchResidualC
    (Q : Type*) [Group Q] : DecidableEq (Q →* ℂˣ) := Classical.decEq _

attribute [local instance] Classical.propDecidable
/-- Helper for Remark 11-11.1-3: in the equality branch `δ.ker = M`, the faithful cyclic layer is
already reduced to the distinguished ambient difference witness. This packages that reduction so
the remaining blocker is stated at the exact pairing level used by the source proof. -/
theorem prime_coatom_kernel_eq_branch_of_difference_divisible
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
    (hdiff :
      ∃ bδ : ℤ,
        ⟪(((δ.toCharacterRing - 1 : R(H0)) : H0 → ℂ)), (ξH : H0 → ℂ)⟫ =
          algebraMap ℤ ℂ (n * bδ)) :
    ∃ bC : ℤ,
      (δ.ker.index : ℂ) * ⟪((1 : R(H0)) : H0 → ℂ), (ξH : H0 → ℂ)⟫ +
        ∑ γ ∈ ((Finset.univ.erase
            (QuotientGroup.lift δ.ker δ (show δ.ker ≤ δ.ker from le_rfl))).filter
          fun γ => γ.ker = ⊥),
          ⟪(((γ.comp (QuotientGroup.mk' δ.ker)).toCharacterRing - 1 : R(H0)) :
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
theorem quotient_comap_map_eq_of_le
    {H0 : Type} [Group H0]
    (K M : Subgroup H0) [K.Normal] (hKM : K ≤ M) :
    Subgroup.comap (QuotientGroup.mk' K) (M.map (QuotientGroup.mk' K)) = M := by
  ext x
  constructor
  · intro hx
    change QuotientGroup.mk' K x ∈ M.map (QuotientGroup.mk' K) at hx
    rcases hx with ⟨m, hm, hmx⟩
    rcases (QuotientGroup.mk'_eq_mk' (N := K)).mp hmx with ⟨z, hz, hxz⟩
    -- The quotient equality differs by an element of `K`, hence by an element of `M`.
    have hzM : z ∈ M := hKM hz
    have hx_eq : x = m * z := hxz.symm
    rw [hx_eq]
    exact M.mul_mem hm hzM
  · intro hx
    -- Any element of `M` maps to the corresponding quotient subgroup by definition.
    exact ⟨x, hx, rfl⟩

/-- Helper for Remark 11-11.1-3: quotienting `H0 ⧸ K` by the image of an overgroup `M`
has the same cardinality as quotienting `H0` directly by `M`. -/
theorem quotient_map_card_eq_quotient_card
    {H0 : Type} [Group H0] [Finite H0]
    (K M : Subgroup H0) [K.Normal] (hKM : K ≤ M) :
    Nat.card (((H0 ⧸ K) ⧸ M.map (QuotientGroup.mk' K))) = Nat.card (H0 ⧸ M) := by
  let L : Subgroup (H0 ⧸ K) := M.map (QuotientGroup.mk' K)
  have hcard :
      Fintype.card (H0 ⧸ Subgroup.comap (QuotientGroup.mk' K) L) =
        Fintype.card ((H0 ⧸ K) ⧸ L) := by
    exact
      Fintype.card_congr
        (Representation.quotient_comap_leftCosetEquiv_local
          (Q := H0) (N := K) L)
  -- The quotient-comap equivalence identifies the iterated quotient with the direct quotient.
  simpa [Nat.card_eq_fintype_card, L, quotient_comap_map_eq_of_le K M hKM] using hcard.symm

/-- Helper for Remark 11-11.1-3: if `H0 ⧸ M` has prime cardinality, then the iterated quotient
`(H0 ⧸ K) ⧸ M.map (mk' K)` also has prime cardinality. -/
theorem quotient_map_prime_card_of_prime_quotient
    {H0 : Type} [Group H0] [Finite H0]
    (K M : Subgroup H0) [K.Normal] (hKM : K ≤ M)
    (hprime : (Nat.card (H0 ⧸ M)).Prime) :
    (Nat.card (((H0 ⧸ K) ⧸ M.map (QuotientGroup.mk' K)))).Prime := by
  -- Replace the iterated quotient cardinality by the direct quotient cardinality.
  rw [quotient_map_card_eq_quotient_card K M hKM]
  exact hprime

/-- Helper for Remark 11-11.1-3: the iterated quotient character obtained from
`((H0 ⧸ δ.ker) ⧸ M.map (mk' δ.ker))` pulls back to the same ambient character as the direct
quotient character transported through Noether's third isomorphism. -/
theorem iterated_quotient_character_pullback_eq_direct_pullback
    {H0 : Type} [Group H0] [Finite H0]
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
    simpa [e, QuotientGroup.quotientQuotientEquivQuotient] using
      (QuotientGroup.quotientQuotientEquivQuotientAux_mk_mk δ.ker M hδker_le_M x)
  have he_symm :
      (QuotientGroup.quotientQuotientEquivQuotient δ.ker M hδker_le_M).symm
          ((x : H0) : H0 ⧸ M) =
        (((x : H0 ⧸ δ.ker) : (H0 ⧸ δ.ker) ⧸ M.map (QuotientGroup.mk' δ.ker))) := by
    -- Apply the inverse equivalence to the direct quotient class to recover the iterated one.
    simpa [e, QuotientGroup.mk'_apply] using congrArg e.symm he
  -- Evaluating either transported character on `x` gives the same scalar.
  simp [MonoidHom.comp_apply, he_symm]

/-- Helper for Remark 11-11.1-3: after applying the quotient pullback pairing to an iterated
quotient-character difference, Noether's third isomorphism rewrites the summand as the ambient
difference term attached to the corresponding direct quotient character on `H0 ⧸ M`. -/
theorem quotient_pullback_pairing_linearMap_difference_via_third_iso
    {H0 : Type} [Group H0] [Finite H0]
    (δ : H0 →* ℂˣ)
    (M : Subgroup H0) [M.Normal]
    (hδker_le_M : δ.ker ≤ M)
    (ξH : R(H0))
    (β : ((H0 ⧸ δ.ker) ⧸ M.map (QuotientGroup.mk' δ.ker)) →* ℂˣ) :
    quotient_pullback_pairing_linearMap δ ξH
        (((β.comp (QuotientGroup.mk' (M.map (QuotientGroup.mk' δ.ker)))).toCharacterRing - 1 :
            R(H0 ⧸ δ.ker))) =
      ⟪(((((β.comp (QuotientGroup.quotientQuotientEquivQuotient δ.ker M hδker_le_M).symm.toMonoidHom).comp
            (QuotientGroup.mk' M)).toCharacterRing - 1 : R(H0)) : H0 → ℂ)),
          (ξH : H0 → ℂ)⟫ := by
  -- First rewrite the quotient-pullback pairing as the ambient erased-difference term for the
  -- iterated quotient character.
  rw [quotient_pullback_pairing_linearMap_difference]
  -- Then transport the pulled-back character itself across the third-isomorphism comparison.
  simp [iterated_quotient_character_pullback_eq_direct_pullback (δ := δ) (M := M) hδker_le_M β]

/-- Helper for Remark 11-11.1-3: the mapped coatom induced-trivial term in the strict branch
pulls back to the ambient coatom induced-trivial pairing. -/
theorem strict_branch_mapped_coatom_pullback_pairing_eq_ambient_coatom_pairing
    {H0 : Type} [Group H0] [Finite H0]
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
  have h := quotient_pullback_pairing_linearMap_induced_trivial
    (β := δ)
    (ξ := ξH)
    (L := M.map (QuotientGroup.mk' δ.ker))
  rw [quotient_comap_map_eq_of_le δ.ker M hδker_le_M] at h
  simpa using h

/-- Helper for Remark 11-11.1-3: transporting the iterated strict-branch quotient-difference
family across Noether's third isomorphism turns the whole sum into the already packaged prime
quotient difference sum. -/
theorem strict_branch_iterated_difference_term_divisible
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
    have hone :
        (((1 : ((H0 ⧸ δ.ker) ⧸ M.map (QuotientGroup.mk' δ.ker)) →* ℂˣ).comp
            (QuotientGroup.mk' (M.map (QuotientGroup.mk' δ.ker)))).toCharacterRing - 1 :
            R(H0 ⧸ δ.ker)) = 0 := by
      rw [MonoidHom.one_comp]
      apply Subtype.ext
      ext h
      simp [MonoidHom.toCharacterRing_apply]
    rw [hone]
    simp
  · have hβ' : β' ≠ 1 := by
      intro hβ'
      apply hβ
      refine MonoidHom.ext fun x ↦ ?_
      -- Transporting the direct quotient equality back across the third-isomorphism equivalence
      -- recovers the original iterated quotient character.
      have hβ'_eval := DFunLike.congr_fun hβ' (e x)
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
        ⟪(((β'.comp (QuotientGroup.mk' M)).toCharacterRing - 1 : R(H0)) : H0 → ℂ),
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
theorem strict_branch_iterated_difference_sum_divisible
    {H0 : Type} [Group H0] [Finite H0] {n : ℤ}
    (δ : H0 →* ℂˣ)
    (M : Subgroup H0) [M.Normal]
    (hδker_lt_M : δ.ker < M)
    (hprime : (Nat.card (H0 ⧸ M)).Prime)
    (ξH : R(H0))
    (hprime_sum :
      ∃ bSum : ℤ,
        ∑ β ∈ ((Finset.univ.erase (1 : (H0 ⧸ M) →* ℂˣ)).filter fun β => β.ker = ⊥),
          ⟪(((β.comp (QuotientGroup.mk' M)).toCharacterRing - 1 : R(H0)) : H0 → ℂ),
              (ξH : H0 → ℂ)⟫ =
          algebraMap ℤ ℂ (n * bSum)) :
    ∃ bSum : ℤ,
      ∑ β : ((H0 ⧸ δ.ker) ⧸ M.map (QuotientGroup.mk' δ.ker)) →* ℂˣ,
        quotient_pullback_pairing_linearMap δ ξH
          (((β.comp (QuotientGroup.mk' (M.map (QuotientGroup.mk' δ.ker)))).toCharacterRing - 1 :
              R(H0 ⧸ δ.ker))) =
        algebraMap ℤ ℂ (n * bSum) := by
  classical
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
    -- Isolate the trivial quotient character so the remaining family matches the packaged
    -- prime-quotient sum.
    simpa [directTerm, add_comm] using
      (Finset.sum_erase_add Finset.univ directTerm
        (Finset.mem_univ (1 : (H0 ⧸ M) →* ℂˣ))).symm
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
  rcases hprime_sum with ⟨bSum, hbSum⟩
  refine ⟨bSum, ?_⟩
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
    _ = algebraMap ℤ ℂ (n * bSum) := hbSum

/-- Helper for Remark 11-11.1-3: the previously attempted quotient-ring reassembly in the strict
branch is impossible. Evaluating it at the identity class would force `δ.ker.index = M.index`,
contradicting `δ.ker < M`. -/
theorem strict_mapped_coatom_ring_reassembly_impossible
    {H0 : Type} [Group H0] [Finite H0]
    (δ : H0 →* ℂˣ)
    (M : Subgroup H0) [M.Normal]
    (hδker_lt_M : δ.ker < M)
    :
    let δq : (H0 ⧸ δ.ker) →* ℂˣ :=
      QuotientGroup.lift δ.ker δ (show δ.ker ≤ δ.ker from le_rfl)
    let Mq : Subgroup (H0 ⧸ δ.ker) := M.map (QuotientGroup.mk' δ.ker)
    ¬ (((δ.ker.index : ℤ) • (1 : R(H0 ⧸ δ.ker)) +
        ∑ γ ∈ ((Finset.univ.erase δq).filter fun γ => γ.ker = ⊥),
          ((γ.toCharacterRing - 1 : R(H0 ⧸ δ.ker)))) =
      Subgroup.characterRingInduction Mq (1 : R(Mq)) +
        ∑ β ∈ ((Finset.univ.erase (1 : (((H0 ⧸ δ.ker) ⧸ Mq) →* ℂˣ))).filter
            fun β => β.ker = ⊥),
          ((β.comp (QuotientGroup.mk' Mq)).toCharacterRing - 1 : R(H0 ⧸ δ.ker))) := by
  classical
  intro δq Mq hreassembly
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
theorem isElementary_of_isCyclic_quotient_local
    {H0 : Type} [Group H0] [Finite H0]
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
Serre's subgroup `R'` of the cyclic kernel quotient. The remaining blocker is therefore the
sharper upgrade from `R'` to the span of proper induced-trivial quotient characters. -/
theorem faithful_quotient_top_layer_mem_elementaryLinearCharacterSpan_of_nontrivial_character
    {H0 : Type} [Group H0] [Finite H0]
    (β : H0 →* ℂˣ) (hβ : β ≠ 1) :
    let βq : (H0 ⧸ β.ker) →* ℂˣ :=
      QuotientGroup.lift β.ker β (show β.ker ≤ β.ker from le_rfl)
    let η : R(H0 ⧸ β.ker) :=
      (β.ker.index : ℤ) • (1 : R(H0 ⧸ β.ker)) +
        ∑ γ ∈ ((Finset.univ.erase βq).filter fun γ => γ.ker = ⊥),
          ((γ.toCharacterRing - 1 : R(H0 ⧸ β.ker)))
    η ∈ R'(H0 ⧸ β.ker) := by
  classical
  dsimp
  have hcyc : IsCyclic (H0 ⧸ β.ker) :=
    kernel_quotient_isCyclic_of_nontrivial_character β hβ
  have hElem : IsElementary (H0 ⧸ β.ker) :=
    isElementary_of_isCyclic_quotient_local hcyc
  -- On the cyclic kernel quotient, Chapter 10 already identifies Serre's subgroup with the full
  -- character ring, so the faithful top layer is automatically an `R'` element.
  rw [elementaryLinearCharacterSpan_eq_top_of_isElementary hElem]
  simp

/-- Helper for Remark 11-11.1-3: in the strict branch, the mapped-coatom block on the kernel
quotient already has pullback pairing divisible by `n`. This packages the coatom-induced term and
the transported iterated quotient-character family into one scalar witness before the residual
quotient correction is addressed. -/
theorem strict_branch_mapped_coatom_block_pairing_divisible
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
    (hprime_sum :
      ∃ bSum : ℤ,
        ∑ β ∈ ((Finset.univ.erase (1 : (H0 ⧸ M) →* ℂˣ)).filter fun β => β.ker = ⊥),
          ⟪(((β.comp (QuotientGroup.mk' M)).toCharacterRing - 1 : R(H0)) : H0 → ℂ),
              (ξH : H0 → ℂ)⟫ =
          algebraMap ℤ ℂ (n * bSum)) :
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
      ∃ bSum : ℤ,
        ∑ β : ((H0 ⧸ δ.ker) ⧸ Mq) →* ℂˣ,
          quotient_pullback_pairing_linearMap δ ξH
            (((β.comp (QuotientGroup.mk' Mq)).toCharacterRing - 1 : R(H0 ⧸ δ.ker))) =
          algebraMap ℤ ℂ (n * bSum) := by
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
  rcases hiterated_sum with ⟨bSum, hbSum⟩
  refine ⟨bM - bSum, ?_⟩
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
          rw [map_sub, map_sum]
    _ = algebraMap ℤ ℂ (n * bM) - algebraMap ℤ ℂ (n * bSum) := by
          rw [hbM, hbSum]
    _ = algebraMap ℤ ℂ (n * (bM - bSum)) := by
          simp [Int.cast_mul, Int.cast_sub, sub_eq_add_neg, mul_add, mul_assoc]

/-- Helper for Remark 11-11.1-3: once every iterated strict-branch quotient-difference term is an
`n`-multiple, the whole iterated quotient-character family packages into a single `n`-multiple.
-/
theorem strict_branch_iterated_quotient_sum_divisible_of_termwise
    {H0 : Type} [Group H0] [Finite H0] {n : ℤ}
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
    ∃ bSum : ℤ,
      ∑ β : ((H0 ⧸ δ.ker) ⧸ M.map (QuotientGroup.mk' δ.ker)) →* ℂˣ,
        quotient_pullback_pairing_linearMap δ ξH
          (((β.comp (QuotientGroup.mk' (M.map (QuotientGroup.mk' δ.ker)))).toCharacterRing - 1 :
              R(H0 ⧸ δ.ker))) =
        algebraMap ℤ ℂ (n * bSum) := by
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
theorem strict_branch_iterated_quotient_sum_divisible
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
    ∃ bSum : ℤ,
      ∑ β : ((H0 ⧸ δ.ker) ⧸ M.map (QuotientGroup.mk' δ.ker)) →* ℂˣ,
        quotient_pullback_pairing_linearMap δ ξH
          (((β.comp (QuotientGroup.mk' (M.map (QuotientGroup.mk' δ.ker)))).toCharacterRing - 1 :
              R(H0 ⧸ δ.ker))) =
        algebraMap ℤ ℂ (n * bSum) := by
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

/-- Branch helper for `strict_branch_nontrivial_nonfaithful_residual_sum_divisible`: a single
nontrivial nonfaithful erased quotient branch is controlled by the smaller-kernel hypothesis. -/
private theorem strict_branch_nonfaithful_branch_term_divisible_local
    {H0 : Type} [Group H0] [Finite H0] {n : ℤ}
    (δ : H0 →* ℂˣ)
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
              algebraMap ℤ ℂ (n * bC))
    (γ : (H0 ⧸ δ.ker) →* ℂˣ)
    (hγ1 : γ ≠ 1)
    (hγker : γ.ker ≠ ⊥) :
    ∃ bγ : ℤ,
      let εγ : H0 →* ℂˣ := γ.comp (QuotientGroup.mk' δ.ker)
      (εγ.ker.index : ℂ) * ⟪((1 : R(H0)) : H0 → ℂ), (ξH : H0 → ℂ)⟫ +
          ∑ θ ∈
              ((Finset.univ.erase
                  (QuotientGroup.lift εγ.ker εγ (show εγ.ker ≤ εγ.ker from le_rfl))).filter
                fun θ => θ.ker = ⊥),
              ⟪(((θ.comp (QuotientGroup.mk' εγ.ker)).toCharacterRing - 1 : R(H0)) :
                    H0 → ℂ),
                  (ξH : H0 → ℂ)⟫ =
        algebraMap ℤ ℂ (n * bγ) := by
  classical
  let ε : H0 →* ℂˣ := γ.comp (QuotientGroup.mk' δ.ker)
  have hε_ne : ε ≠ 1 := by
    intro hε
    apply hγ1
    refine MonoidHom.ext fun x ↦ ?_
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective δ.ker x
    simpa [ε] using DFunLike.congr_fun hε y
  have hε_lt : ε.ker.index < δ.ker.index := by
    -- Nonfaithful erased quotient characters strictly enlarge the ambient kernel.
    simpa [ε] using
      kernel_growth_measure_decreases_on_nonfaithful_erased_branch δ γ hγker
  -- The smaller-kernel owner theorem closes each nontrivial nonfaithful branch individually.
  simpa [ε] using hsmaller ε hε_ne hε_lt

/-- Helper for Remark 11-11.1-3: after removing the trivial quotient character, every
nonfaithful erased quotient branch in the strict branch is already controlled by the
smaller-kernel hypothesis, so the whole residual family packages into a single `n`-multiple. -/
theorem strict_branch_nontrivial_nonfaithful_residual_sum_divisible
    {H0 : Type} [Group H0] [Finite H0] {n : ℤ}
    (δ : H0 →* ℂˣ)
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
      ∑ γ ∈ (((Finset.univ.erase δq).filter fun γ => γ.ker ≠ ⊥).erase 1), residualTerm γ =
        algebraMap ℤ ℂ (n * bNF) := by
  classical
  -- Introduce the statement-level `let`s as local definitions instead of zeta-expanding them;
  -- this keeps the goal terms small enough for the default elaboration budget.
  intro δq residualTerm
  have hterm :
      ∀ γ ∈ (((Finset.univ.erase δq).filter fun γ => γ.ker ≠ ⊥).erase 1),
        ∃ bγ : ℤ, residualTerm γ = algebraMap ℤ ℂ (n * bγ) := by
    intro γ hγ
    simp only [Finset.mem_erase, Finset.mem_filter, Finset.mem_univ, true_and, and_true] at hγ
    -- Each nontrivial nonfaithful branch is handled by the dedicated branch helper.
    exact strict_branch_nonfaithful_branch_term_divisible_local δ ξH hsmaller γ hγ.1 hγ.2.2
  -- Package the termwise smaller-kernel witnesses into one finite residual sum.
  exact finset_sum_int_multiples _ hterm

/-- Helper for Remark 11-11.1-3: in the strict-branch residual package, the exceptional erased
nonfaithful term at `γ = 1` is exactly the pullback pairing of the trivial quotient character. -/
theorem strict_branch_trivial_nonfaithful_erased_branch_identity
    {H0 : Type} [Group H0] [Finite H0]
    (δ : H0 →* ℂˣ)
    (ξH : R(H0)) :
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
    residualTerm (1 : (H0 ⧸ δ.ker) →* ℂˣ) =
      quotient_pullback_pairing_linearMap δ ξH (1 : R(H0 ⧸ δ.ker)) := by
  classical
  dsimp only
  -- Evaluate the residual term at the trivial quotient character and collapse the now-empty
  -- erased quotient family.
  have hterm_zero :
      ∀ θ ∈ ((Finset.univ.erase
            (QuotientGroup.lift ((1 : (H0 ⧸ δ.ker) →* ℂˣ).comp (QuotientGroup.mk' δ.ker)).ker
              ((1 : (H0 ⧸ δ.ker) →* ℂˣ).comp (QuotientGroup.mk' δ.ker))
              (le_rfl))).filter
          fun θ => θ.ker = ⊥),
        ⟪(((θ.comp (QuotientGroup.mk'
                (((1 : (H0 ⧸ δ.ker) →* ℂˣ).comp (QuotientGroup.mk' δ.ker)).ker))).toCharacterRing -
              1 : R(H0)) : H0 → ℂ),
            (ξH : H0 → ℂ)⟫ = 0 := by
    intro θ _
    have hcomp :
        θ.comp (QuotientGroup.mk'
            (((1 : (H0 ⧸ δ.ker) →* ℂˣ).comp (QuotientGroup.mk' δ.ker)).ker)) = 1 := by
      refine MonoidHom.ext fun x ↦ ?_
      have hx :
          QuotientGroup.mk'
              (((1 : (H0 ⧸ δ.ker) →* ℂˣ).comp (QuotientGroup.mk' δ.ker)).ker) x = 1 :=
        (QuotientGroup.eq_one_iff x).mpr (by simp [MonoidHom.mem_ker])
      simp only [MonoidHom.comp_apply, MonoidHom.one_apply]
      rw [hx]
      exact map_one θ
    have hzero :
        ((θ.comp (QuotientGroup.mk'
              (((1 : (H0 ⧸ δ.ker) →* ℂˣ).comp (QuotientGroup.mk' δ.ker)).ker))).toCharacterRing -
            1 : R(H0)) = 0 := by
      rw [hcomp]
      apply Subtype.ext
      ext h
      simp [MonoidHom.toCharacterRing_apply]
    rw [hzero]
    simp [Representation.groupFunctionPairingOverField]
  have hidx :
      ((((1 : (H0 ⧸ δ.ker) →* ℂˣ).comp (QuotientGroup.mk' δ.ker)).ker.index : ℕ) : ℂ) = 1 := by
    have hker :
        ((1 : (H0 ⧸ δ.ker) →* ℂˣ).comp (QuotientGroup.mk' δ.ker)).ker = ⊤ := by
      ext x
      simp [MonoidHom.mem_ker]
    rw [hker]
    simp
  rw [Finset.sum_eq_zero hterm_zero, hidx, quotient_pullback_pairing_linearMap_one]
  ring

/-- Helper for Remark 11-11.1-3: in the strict branch, the full nonfaithful erased quotient
family splits at the exceptional term `γ = 1`. -/
theorem strict_branch_nonfaithful_residual_sum_split_at_one
    {H0 : Type} [Group H0] [Finite H0]
    (δ : H0 →* ℂˣ)
    (ξH : R(H0))
    (hδ : δ ≠ 1) :
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
      residualTerm (1 : (H0 ⧸ δ.ker) →* ℂˣ) +
        ∑ γ ∈ (((Finset.univ.erase δq).filter fun γ => γ.ker ≠ ⊥).erase 1), residualTerm γ := by
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
    refine MonoidHom.ext fun x ↦ ?_
    have hxker : x ∈ (1 : (H0 ⧸ δ.ker) →* ℂˣ).ker := by
      simp [MonoidHom.mem_ker]
    have hxbot : x ∈ (⊥ : Subgroup (H0 ⧸ δ.ker)) := by
      simpa [hker] using hxker
    have hxone : x = 1 := by
      simpa using hxbot
    simpa [hxone]
  -- Isolate the exceptional erased nonfaithful term before packaging the remaining residual
  -- branch by the smaller-kernel theorem.
  exact (Finset.add_sum_erase _ _ hone_mem).symm


end CharacterizationOfCharacters

end Representation
