import Mathlib
import LinearRepresentations_Serre_1977.Chap10.Definition_10_10_1_3
import LinearRepresentations_Serre_1977.Chap10.Remark_10_10_5_4
import LinearRepresentations_Serre_1977.Chap11.Remark_11_11_1_3.TensorCharacterRingRestriction
import LinearRepresentations_Serre_1977.Chap11.Remark_11_11_1_3.RestrictionFamily
import LinearRepresentations_Serre_1977.Chap11.Remark_11_11_1_3.ElementaryConjugation
import LinearRepresentations_Serre_1977.Chap11.Remark_11_11_1_3.ElementaryDetection
import LinearRepresentations_Serre_1977.Chap11.Remark_11_11_1_3.IntegralRestrictionSplitting
import LinearRepresentations_Serre_1977.Chap11.Remark_11_11_1_3.ElementaryCoherence
import LinearRepresentations_Serre_1977.Chap11.Remark_11_11_1_3.SubgroupLinearPairing
import LinearRepresentations_Serre_1977.Chap11.Remark_11_11_1_3.TopLocalPairing
import LinearRepresentations_Serre_1977.Chap11.Remark_11_11_1_3.CoatomDivisibility

noncomputable section

universe v

namespace Representation

section CharacterizationOfCharacters

open scoped Pointwise Representation SubgroupInduction TensorProduct

variable {G : Type} [Group G] [Finite G]
variable {A : Type v} [CommRing A]

local notation:max s " •ᶜ " H => (MulAut.conj s • H : Subgroup G)

/-- Helper for Remark 11-11.1-3: every subgroup of a finite group is finite. -/
local instance fintypeHelperLocalKernelQuotientCharacters1 (H : Subgroup G) : Fintype H := Fintype.ofFinite H

/-- Helper for Remark 11-11.1-3: the degree-one characters of a finite group form a finite type. -/
noncomputable local instance fintypeHelperLocalKernelQuotientCharacters2
    (Q : Type*) [Group Q] [Finite Q] : Fintype (Q →* ℂˣ) := Fintype.ofFinite _

/-- Helper for Remark 11-11.1-3: classical decidable equality for degree-one characters. -/
noncomputable local instance fintypeHelperLocalKernelQuotientCharacters3
    (Q : Type*) [Group Q] [Finite Q] : DecidableEq (Q →* ℂˣ) := Classical.decEq _

attribute [local instance] Classical.propDecidable
/-- Helper for Remark 11-11.1-3: normalizing the proper-subgroup transport theorem at a kernel
shows that it lands on the induced trivial character from that kernel, not yet on the ambient
top-difference term. This is the precise input expected by the later quotient recursion. -/
theorem kernel_branch_transport_target_normal_form
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
  have hchar : ((1 : β.ker →* ℂˣ).toRepresentation.character) = (1 : β.ker → ℂ) := by
    ext k
    simp
  simpa [hchar] using
    proper_induced_pairing_divisible_of_transport_pairing_int_divisible
      X hXelem hdx H sH hsH β.ker (1 : β.ker →* ℂˣ)

/-- Helper for Remark 11-11.1-3: a nontrivial ambient linear character stays nontrivial after
factoring through the quotient by its kernel. -/
theorem kernel_quotient_character_ne_one
    {H0 : Type} [Group H0]
    (β : H0 →* ℂˣ) (hβ : β ≠ 1) :
    let βq : (H0 ⧸ β.ker) →* ℂˣ :=
      QuotientGroup.lift β.ker β (show β.ker ≤ β.ker from le_rfl)
    βq ≠ 1 := by
  classical
  dsimp
  intro hβq
  apply hβ
  refine MonoidHom.ext fun x ↦ ?_
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
theorem erased_quotient_character_kernel_eq_of_quotient_ker_eq_bot
    {H0 : Type} [Group H0]
    (β : H0 →* ℂˣ) (γ : (H0 ⧸ β.ker) →* ℂˣ) (hγker : γ.ker = ⊥) :
    (γ.comp (QuotientGroup.mk' β.ker)).ker = β.ker := by
  -- Rewrite both kernels as comaps along the quotient map and collapse the quotient-side kernel
  -- to `⊥`.
  conv_rhs => rw [← QuotientGroup.ker_mk' β.ker]
  rw [← MonoidHom.comap_ker, hγker, MonoidHom.comap_bot]

/-- Helper for Remark 11-11.1-3: strict kernel growth in the erased quotient-character branch
occurs exactly when the quotient character itself has nontrivial kernel. -/
theorem erased_quotient_character_kernel_lt_of_quotient_ker_ne_bot
    {H0 : Type} [Group H0]
    (β : H0 →* ℂˣ) (γ : (H0 ⧸ β.ker) →* ℂˣ) (hγker : γ.ker ≠ ⊥) :
    β.ker < (γ.comp (QuotientGroup.mk' β.ker)).ker := by
  -- Route correction: `γ ≠ βq` does not force strict kernel growth. The correct source-faithful
  -- split is between quotient characters with trivial kernel and those with nontrivial kernel.
  conv_lhs => rw [← QuotientGroup.ker_mk' β.ker]
  rw [← MonoidHom.comap_ker]
  exact
    (Subgroup.comap_lt_comap_of_surjective (f := QuotientGroup.mk' β.ker)
      (hf := QuotientGroup.mk'_surjective β.ker)).2 <|
      bot_lt_iff_ne_bot.mpr hγker

/-- Helper for Remark 11-11.1-3: isolating the quotient character induced by `β` splits the
kernel-induced pairing into the trivial line, the distinguished ambient difference term, and the
remaining quotient-character differences. -/
theorem kernel_induced_pairing_decomposes_with_distinguished_difference
    {H0 : Type} [Group H0] [Finite H0]
    (β : H0 →* ℂˣ) (ξ : R(H0)) :
    let βq : (H0 ⧸ β.ker) →* ℂˣ :=
      QuotientGroup.lift β.ker β (show β.ker ≤ β.ker from le_rfl)
    ⟪(Subgroup.characterRingInduction β.ker (1 : R(β.ker)) : H0 → ℂ), (ξ : H0 → ℂ)⟫ =
      (β.ker.index : ℂ) * ⟪((1 : R(H0)) : H0 → ℂ), (ξ : H0 → ℂ)⟫ +
        ⟪(((β.toCharacterRing - 1 : R(H0)) : H0 → ℂ)), (ξ : H0 → ℂ)⟫ +
          ∑ γ ∈ Finset.univ.erase βq,
            ⟪(((γ.comp (QuotientGroup.mk' β.ker)).toCharacterRing - 1 : R(H0)) : H0 → ℂ),
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
    ⟪(((γ.comp (QuotientGroup.mk' β.ker)).toCharacterRing - 1 : R(H0)) : H0 → ℂ),
        (ξ : H0 → ℂ)⟫
  have hβ_factor : β = βq.comp (QuotientGroup.mk' β.ker) := by
    -- The chosen quotient character is defined precisely by factoring `β` through `β.ker`.
    simpa [βq] using
      (QuotientGroup.lift_comp_mk' β.ker β (show β.ker ≤ β.ker from le_rfl)).symm
  have hsplit :
      ∑ γ : (H0 ⧸ β.ker) →* ℂˣ, term γ =
        term βq + ∑ γ ∈ Finset.univ.erase βq, term γ := by
    -- Isolate the distinguished quotient character from the full quotient-character sum.
    simpa [term] using
      (Finset.sum_erase_add (s := Finset.univ) (a := βq) (by simp)).symm
  have hβq_term :
      term βq =
        ⟪(((β.toCharacterRing - 1 : R(H0)) : H0 → ℂ)), (ξ : H0 → ℂ)⟫ := by
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
          (term βq + ∑ γ ∈ Finset.univ.erase βq, term γ) := by
            rw [hsplit]
    _ =
        (β.ker.index : ℂ) * ⟪((1 : R(H0)) : H0 → ℂ), (ξ : H0 → ℂ)⟫ +
          ⟪(((β.toCharacterRing - 1 : R(H0)) : H0 → ℂ)), (ξ : H0 → ℂ)⟫ +
            ∑ γ ∈ Finset.univ.erase βq, term γ := by
              simpa [hβq_term, add_assoc]

/-- Helper for Remark 11-11.1-3: scaling the trivial-line pairing by the kernel index preserves
`n`-divisibility in the kernel-recursion branch. -/
theorem scaled_top_local_trivial_pairing_divisible_of_residual_family
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
  let XH : Finset (Subgroup H.1) := Finset.univ
  let ψH : (J : XH) → R(J.1) := fun J ↦
    Subgroup.characterRingTransport
      (J.1.equivMapOfInjective H.1.subtype H.1.subtype_injective)
      (x ⟨J.1.map H.1.subtype,
        (hXelem (J.1.map H.1.subtype)).2 <|
          isElementary_of_mulEquiv_local
            (J.1.equivMapOfInjective H.1.subtype H.1.subtype_injective)
            (subgroup_isElementary_of_isElementary_local J.1 ((hXelem H.1).1 H.2))⟩)
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
theorem erased_quotient_character_difference_divisible_of_comp_eq_one
    (X : Finset (Subgroup G))
    (hXelem : ∀ H : Subgroup G, H ∈ X ↔ IsElementary H)
    {x : (H : X) → R(H.1)} {t : elementary_coherence_target X hXelem} {n : ℤ}
    (H : X)
    (sH : ((J : (Finset.univ : Finset (Subgroup H.1))) → R(J.1)) →ₗ[ℤ] R(H.1))
    (β : H.1 →* ℂˣ)
    (γ : (H.1 ⧸ β.ker) →* ℂˣ)
    (hδ : γ.comp (QuotientGroup.mk' β.ker) = 1) :
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
  refine ⟨0, ?_⟩
  -- When the lifted quotient character is trivial, the ambient difference character vanishes.
  have hzero :
      (((γ.comp (QuotientGroup.mk' β.ker)).toCharacterRing - 1 : R(H.1))) = 0 := by
    rw [hδ, Subgroup.toCharacterRing_one]
    exact sub_self 1
  -- The pairing with the zero difference term is therefore the zero `n`-multiple.
  rw [hzero]
  simp [Representation.groupFunctionPairingOverField]

/-- Helper for Remark 11-11.1-3: a nonfaithful erased quotient character enlarges the ambient
kernel, so the kernel-index measure used in the owner recursion strictly decreases. -/
theorem kernel_growth_measure_decreases_on_nonfaithful_erased_branch
    {H0 : Type} [Group H0] [Finite H0]
    (β : H0 →* ℂˣ) (γ : (H0 ⧸ β.ker) →* ℂˣ) (hγker : γ.ker ≠ ⊥) :
    (γ.comp (QuotientGroup.mk' β.ker)).ker.index < β.ker.index := by
  -- Convert the strict kernel inclusion into the strict index decrease needed by strong induction.
  exact
    Subgroup.index_strictAnti
      (erased_quotient_character_kernel_lt_of_quotient_ker_ne_bot β γ hγker)

/-- Helper for Remark 11-11.1-3: on a prime-order quotient, every nontrivial lifted linear
character has kernel exactly the coatom used to form the quotient. -/
theorem lifted_prime_quotient_character_kernel_eq_coatom
    {H0 : Type} [Group H0] [Finite H0]
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
      refine MonoidHom.ext fun x ↦ ?_
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
theorem lifted_prime_coatom_character_has_smaller_kernel_index
    {H0 : Type} [Group H0] [Finite H0]
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
    refine MonoidHom.ext fun y ↦ ?_
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective M y
    -- Evaluate the lifted equality on a representative of `y` to recover the quotient character.
    simpa using DFunLike.congr_fun hε x
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
theorem prime_coatom_nonfaithful_erased_branch_vanishes
    {H0 : Type} [Group H0] [Finite H0]
    (M : Subgroup H0) [M.Normal]
    (hprime : (Nat.card (H0 ⧸ M)).Prime)
    (β : (H0 ⧸ M) →* ℂˣ) (hβ : β ≠ 1)
    (ξ : R(H0)) :
    ∑ γ ∈ ((Finset.univ.erase β).filter fun γ => γ.ker ≠ ⊥),
      ⟪(((γ.comp (QuotientGroup.mk' M)).toCharacterRing - 1 : R(H0)) : H0 → ℂ),
          (ξ : H0 → ℂ)⟫ = 0 := by
  classical
  letI : Fact (Nat.card (H0 ⧸ M)).Prime := ⟨hprime⟩
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
      · refine MonoidHom.ext fun x ↦ ?_
        have hxker : x ∈ γ.ker := by
          rw [hγker]
          simp
        -- Kernel equal to `⊤` means the quotient character is trivial.
        simpa [MonoidHom.mem_ker] using hxker
    · intro hγ
      subst hγ
      constructor
      · simpa [eq_comm] using hβ
      · haveI : Nontrivial (H0 ⧸ M) :=
          Finite.one_lt_card_iff_nontrivial.mp hprime.one_lt
        simpa using (Subgroup.top_ne_bot (G := H0 ⧸ M))
  -- After identifying the filtered branch with the singleton `{1}`, the difference term is zero.
  rw [hfilter]
  have hzero :
      (((1 : (H0 ⧸ M) →* ℂˣ).comp (QuotientGroup.mk' M)).toCharacterRing - 1 : R(H0)) = 0 := by
    rw [MonoidHom.one_comp]
    apply Subtype.ext
    ext h
    simp [MonoidHom.toCharacterRing_apply]
  simp [hzero, Representation.groupFunctionPairingOverField]

/-- Helper for Remark 11-11.1-3: on a prime quotient, every nontrivial linear character is
faithful, so filtering the erased character family by `ker = ⊥` does not remove any term. -/
theorem prime_quotient_faithful_filter_eq_erase_one
    {H0 : Type} [Group H0] [Finite H0]
    (M : Subgroup H0) [M.Normal]
    (hprime : (Nat.card (H0 ⧸ M)).Prime) :
    ((Finset.univ.erase (1 : (H0 ⧸ M) →* ℂˣ)).filter fun γ => γ.ker = ⊥) =
      Finset.univ.erase (1 : (H0 ⧸ M) →* ℂˣ) := by
  classical
  letI : Fact (Nat.card (H0 ⧸ M)).Prime := ⟨hprime⟩
  apply Finset.ext
  intro γ
  simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_univ, true_and, and_true]
  constructor
  · intro hγ
    exact hγ.1
  · intro hγ
    refine ⟨hγ, ?_⟩
    rcases Subgroup.eq_bot_or_eq_top_of_prime_card γ.ker with hγker | hγker
    · exact hγker
    · exfalso
      apply hγ
      refine MonoidHom.ext fun x ↦ ?_
      have hxker : x ∈ γ.ker := by
        rw [hγker]
        simp
      -- On a prime quotient, kernel `⊤` forces the character to be trivial.
      simpa [MonoidHom.mem_ker] using hxker

/-- Helper for Remark 11-11.1-3: once every nontrivial character of the prime quotient `H0 ⧸ M`
has an `n`-divisible lifted difference pairing, the whole faithful lifted quotient block is an
`n`-multiple. This isolates the arithmetic part of the strict coatom branch from the remaining
reassembly identity. -/
theorem prime_quotient_faithful_lift_difference_sum_divisible
    {H0 : Type} [Group H0] [Finite H0] {n : ℤ}
    (M : Subgroup H0) [M.Normal]
    (hprime : (Nat.card (H0 ⧸ M)).Prime)
    (ξH : R(H0))
    (hquotdiff :
      ∀ β : (H0 ⧸ M) →* ℂˣ, β ≠ 1 →
        ∃ bβ : ℤ,
          ⟪(((β.comp (QuotientGroup.mk' M)).toCharacterRing - 1 : R(H0)) : H0 → ℂ),
              (ξH : H0 → ℂ)⟫ =
            algebraMap ℤ ℂ (n * bβ)) :
    ∃ bSum : ℤ,
      ∑ β ∈ ((Finset.univ.erase (1 : (H0 ⧸ M) →* ℂˣ)).filter fun β => β.ker = ⊥),
        ⟪(((β.comp (QuotientGroup.mk' M)).toCharacterRing - 1 : R(H0)) : H0 → ℂ),
            (ξH : H0 → ℂ)⟫ =
        algebraMap ℤ ℂ (n * bSum) := by
  classical
  obtain ⟨bSum, hbSum⟩ :=
    finset_sum_int_multiples
      (s := Finset.univ.erase (1 : (H0 ⧸ M) →* ℂˣ))
      (f := fun β : (H0 ⧸ M) →* ℂˣ ↦
        ⟪(((β.comp (QuotientGroup.mk' M)).toCharacterRing - 1 : R(H0)) : H0 → ℂ),
            (ξH : H0 → ℂ)⟫)
      (n := n) fun β hβ ↦ by
        -- On the erased quotient family, membership is exactly the nontriviality needed to call
        -- the strict-branch lift hypothesis.
        exact hquotdiff β (by simpa [Finset.mem_erase] using hβ)
  -- On a prime quotient the faithful filter is redundant, so the packaged finite sum already has
  -- the target shape.
  refine ⟨bSum, ?_⟩
  simpa [prime_quotient_faithful_filter_eq_erase_one (M := M) hprime] using hbSum

/-- Helper for Remark 11-11.1-3: the quotient by the kernel of a degree-`1` character is cyclic,
because it identifies with the cyclic image of that character. -/
theorem kernel_quotient_isCyclic_of_nontrivial_character
    {H0 : Type} [Group H0] [Finite H0]
    (β : H0 →* ℂˣ) (_hβ : β ≠ 1) :
    IsCyclic (H0 ⧸ β.ker) := by
  let e : H0 ⧸ β.ker ≃* β.range := QuotientGroup.quotientKerEquivRange β
  letI : IsCyclic β.range := Representation.degree_one_character_range_isCyclic β
  -- Transport cyclicity across the canonical quotient-range equivalence.
  exact e.isCyclic.mpr inferInstance

/-- Helper for Remark 11-11.1-3: the quotient by the kernel of a degree-`1` character is
commutative, because it identifies with a subgroup of `ℂˣ`. -/
theorem kernel_quotient_mul_comm_of_nontrivial_character
    {H0 : Type} [Group H0] [Finite H0]
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
theorem kernel_quotient_distinguished_character_data
    {H0 : Type} [Group H0] [Finite H0]
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

/-- Helper for Remark 11-11.1-3: if the chosen coatom already equals the kernel, then the coatom
identity reduces the faithful cyclic layer to the coatom induced-trivial pairing minus the
distinguished ambient difference term. -/
theorem faithful_cyclic_layer_pairing_eq_kernel_induced_minus_distinguished_difference
    {H0 : Type} [Group H0] [Finite H0]
    (δ : H0 →* ℂˣ) (hδ : δ ≠ 1)
    (M : Subgroup H0) [M.Normal]
    (ξH : R(H0))
    (hEq : δ.ker = M)
    (hprime : (Nat.card (H0 ⧸ M)).Prime) :
    (δ.ker.index : ℂ) * ⟪((1 : R(H0)) : H0 → ℂ), (ξH : H0 → ℂ)⟫ +
        ∑ γ ∈ ((Finset.univ.erase
            (QuotientGroup.lift δ.ker δ (show δ.ker ≤ δ.ker from le_rfl))).filter
          fun γ => γ.ker = ⊥),
          ⟪(((γ.comp (QuotientGroup.mk' δ.ker)).toCharacterRing - 1 : R(H0)) :
                H0 → ℂ),
              (ξH : H0 → ℂ)⟫ =
      ⟪(Subgroup.characterRingInduction M (1 : R(M)) : H0 → ℂ), (ξH : H0 → ℂ)⟫ -
        ⟪(((δ.toCharacterRing - 1 : R(H0)) : H0 → ℂ)), (ξH : H0 → ℂ)⟫ := by
  classical
  subst hEq
  let δq : (H0 ⧸ δ.ker) →* ℂˣ :=
    QuotientGroup.lift δ.ker δ (show δ.ker ≤ δ.ker from le_rfl)
  let term : ((H0 ⧸ δ.ker) →* ℂˣ) → ℂ := fun γ ↦
    ⟪(((γ.comp (QuotientGroup.mk' δ.ker)).toCharacterRing - 1 : R(H0)) : H0 → ℂ),
        (ξH : H0 → ℂ)⟫
  obtain ⟨_, hδq_ne, _, _⟩ := kernel_quotient_distinguished_character_data δ hδ
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
    -- On the prime quotient above the chosen coatom, the only erased nonfaithful term is the
    -- trivial character, so its ambient difference contribution vanishes.
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
  -- Move the distinguished difference term to the right to isolate the faithful cyclic layer.
  exact eq_sub_iff_add_eq.mpr <| by
    simpa [add_comm, add_left_comm, add_assoc] using hrewrite.symm

/-- Helper for Remark 11-11.1-3: if the chosen coatom already equals the kernel, then the coatom
identity reduces the faithful cyclic layer to the coatom induced-trivial pairing minus the
distinguished ambient difference term. -/
theorem faithful_cyclic_layer_of_kernel_eq_chosen_coatom_of_difference_divisible
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
  classical
  subst hEq
  let δq : (H0 ⧸ δ.ker) →* ℂˣ :=
    QuotientGroup.lift δ.ker δ (show δ.ker ≤ δ.ker from le_rfl)
  let term : ((H0 ⧸ δ.ker) →* ℂˣ) → ℂ := fun γ ↦
    ⟪(((γ.comp (QuotientGroup.mk' δ.ker)).toCharacterRing - 1 : R(H0)) : H0 → ℂ),
        (ξH : H0 → ℂ)⟫
  obtain ⟨_, hδq_ne, _, _⟩ := kernel_quotient_distinguished_character_data δ hδ
  rcases hMpair with ⟨bM, hbM⟩
  rcases hdiff with ⟨bδ, hbδ⟩
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
    -- On the prime quotient above the chosen coatom, the only erased nonfaithful term is the
    -- trivial character, so its ambient difference contribution vanishes.
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
      (δ.ker.index : ℂ) * ⟪((1 : R(H0)) : H0 → ℂ), (ξH : H0 → ℂ)⟫ +
          ∑ γ ∈ ((Finset.univ.erase δq).filter fun γ => γ.ker = ⊥), term γ =
        ⟪(Subgroup.characterRingInduction δ.ker (1 : R(δ.ker)) : H0 → ℂ), (ξH : H0 → ℂ)⟫ -
          ⟪(((δ.toCharacterRing - 1 : R(H0)) : H0 → ℂ)), (ξH : H0 → ℂ)⟫ := by
    -- Move the distinguished difference term to the right to isolate the faithful cyclic layer.
    exact eq_sub_iff_add_eq.mpr <| by
      simpa [add_comm, add_left_comm, add_assoc] using hrewrite.symm
  refine ⟨bM - bδ, ?_⟩
  -- Combine the coatom induced-trivial witness with the distinguished-difference witness by
  -- subtraction.
  calc
    (δ.ker.index : ℂ) * ⟪((1 : R(H0)) : H0 → ℂ), (ξH : H0 → ℂ)⟫ +
        ∑ γ ∈ ((Finset.univ.erase δq).filter fun γ => γ.ker = ⊥), term γ =
      ⟪(Subgroup.characterRingInduction δ.ker (1 : R(δ.ker)) : H0 → ℂ), (ξH : H0 → ℂ)⟫ -
        ⟪(((δ.toCharacterRing - 1 : R(H0)) : H0 → ℂ)), (ξH : H0 → ℂ)⟫ := htarget
    _ = algebraMap ℤ ℂ (n * bM) - algebraMap ℤ ℂ (n * bδ) := by
          rw [hbM, hbδ]
    _ = algebraMap ℤ ℂ (n * (bM - bδ)) := by
          simp [Int.cast_mul, Int.cast_sub, sub_eq_add_neg, mul_add, mul_assoc]


end CharacterizationOfCharacters

end Representation
