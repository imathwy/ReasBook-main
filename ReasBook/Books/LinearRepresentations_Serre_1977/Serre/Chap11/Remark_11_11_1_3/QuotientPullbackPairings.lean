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

noncomputable section

universe v

namespace Representation

section CharacterizationOfCharacters

open scoped Pointwise Representation SubgroupInduction TensorProduct

variable {G : Type} [Group G] [Finite G]
variable {A : Type v} [CommRing A]

local notation:max s " •ᶜ " H => (MulAut.conj s • H : Subgroup G)

/-- Helper for Remark 11-11.1-3: every subgroup of a finite group is finite. -/
local instance fintypeHelperLocalQuotientPullbackPairings1 (H : Subgroup G) : Fintype H := Fintype.ofFinite H

/-- Helper for Remark 11-11.1-3: quotients of finite groups are finite types. -/
noncomputable local instance fintypeHelperLocalQuotientPullbackPairings2
    (Q : Type*) [Group Q] [Finite Q] (M : Subgroup Q) [M.Normal] : Fintype (Q ⧸ M) :=
  Fintype.ofFinite _

/-- Helper for Remark 11-11.1-3: the degree-one characters of a finite group form a finite type. -/
noncomputable local instance fintypeHelperLocalQuotientPullbackPairings3
    (Q : Type*) [Group Q] [Finite Q] : Fintype (Q →* ℂˣ) := Fintype.ofFinite _

/-- Helper for Remark 11-11.1-3: one canonical classical decidable equality for characters. -/
noncomputable local instance (priority := 2000) fintypeHelperLocalQuotientPullbackPairings4
    (Q : Type*) [Group Q] : DecidableEq (Q →* ℂˣ) := Classical.decEq _

attribute [local instance] Classical.propDecidable
/-- Helper for Remark 11-11.1-3: once the cyclic top layer is expressed as a finite
`ℤ`-combination of proper induced-trivial pairings, the local proper-branch theorem closes the
whole finite sum at once. -/
theorem interval_overgroup_pairing_sum_divisible_of_local_proper_branch
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
    (S : Finset (Subgroup H.1)) (a : Subgroup H.1 → ℤ)
    (hS : ∀ J ∈ S, J < ⊤) :
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
      ∑ J ∈ S,
        algebraMap ℤ ℂ (a J) *
          ⟪(Subgroup.characterRingInduction J (1 : R(J)) : H.1 → ℂ), (ξH : H.1 → ℂ)⟫ =
        algebraMap ℤ ℂ (n * b) := by
  classical
  dsimp
  have hterm :
      ∀ J ∈ S,
        ∃ bJ : ℤ,
          algebraMap ℤ ℂ (a J) *
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
            algebraMap ℤ ℂ (n * bJ) := by
    intro J hJ
    -- Close each weighted proper-overgroup summand by rescaling the one-term proper-branch
    -- witness.
    simpa using
      int_multiple_of_proper_induced_trivial_pairing_divisible_of_local_proper_branch
        X hXelem hdx H sH hsH hproper (a J) J (hS J hJ)
  obtain ⟨b, hb⟩ :=
    finset_sum_int_multiples
      (s := S)
      (f := fun J ↦
        algebraMap ℤ ℂ (a J) *
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
                              ((hXelem H.1).1 H.2))⟩)) : R(H.1)) : H.1 → ℂ)⟫)
      (n := n) hterm
  exact ⟨b, hb⟩

/-- Helper for Remark 11-11.1-3: pulling a proper quotient subgroup back along the quotient map
produces a proper overgroup of the kernel. This isolates the subgroup-transport bookkeeping from
the remaining cyclic pairing rewrite. -/
theorem quotient_subgroup_comap_above_kernel_and_lt_top
    {H0 : Type} [Group H0]
    (K : Subgroup H0) [K.Normal] (L : Subgroup (H0 ⧸ K)) (hL : L < ⊤) :
    K ≤ Subgroup.comap (QuotientGroup.mk' K) L ∧
      Subgroup.comap (QuotientGroup.mk' K) L < ⊤ := by
  refine ⟨?_, ?_⟩
  · intro x hx
    -- Elements of the kernel map to `1`, and every subgroup contains `1`.
    change QuotientGroup.mk' K x ∈ L
    have hxone : QuotientGroup.mk' K x = 1 := by
      exact (QuotientGroup.eq_one_iff _).2 hx
    simpa [hxone] using L.one_mem
  · refine lt_top_iff_ne_top.mpr ?_
    intro hcomap_top
    apply hL.ne
    -- The quotient map is surjective, so equality after comap forces equality downstairs.
    apply Subgroup.comap_injective (f := QuotientGroup.mk' K) (QuotientGroup.mk'_surjective K)
    simpa [hcomap_top]

/-- Helper for Remark 11-11.1-3: a membership in the span of a ranged family can be repackaged as
an explicit finitely supported `ℤ`-linear combination of that family. -/
theorem exists_finsupp_eq_sum_of_mem_span_range
    {ι : Type*} {M : Type*} [AddCommGroup M] [Module ℤ M]
    (v : ι → M) {x : M} (hx : x ∈ Submodule.span ℤ (Set.range v)) :
    ∃ c : ι →₀ ℤ, x = c.sum (fun i n ↦ n • v i) := by
  rcases Finsupp.mem_span_range_iff_exists_finsupp.1 hx with ⟨c, hc⟩
  -- Record the span witness as a single finitely supported sum so later subgroup bookkeeping only
  -- has to rearrange one finite support.
  refine ⟨c, ?_⟩
  rw [← hc]
  refine Finsupp.sum_congr fun i _ ↦ ?_
  exact Int.cast_smul_eq_zsmul ℤ (c i) (v i)

/-- Helper for Remark 11-11.1-3: a finitely supported sum indexed by subgroup data can be rewritten
as a finite sum over the ambient subgroup lattice with coefficient function `a`. -/
theorem subgroup_finsupp_sum_eq_finset_sum
    {H0 : Type} [Group H0]
    {M : Type*} [AddCommGroup M] [Module ℤ M]
    {P : Subgroup H0 → Prop}
    (v : Subgroup H0 → M)
    (c : {J : Subgroup H0 // P J} →₀ ℤ) :
    ∃ (S : Finset (Subgroup H0)) (a : Subgroup H0 → ℤ),
      (∀ J ∈ S, P J) ∧
        c.sum (fun i n ↦ n • v i.1) = ∑ J ∈ S, a J • v J := by
  classical
  let e : {J : Subgroup H0 // P J} ↪ Subgroup H0 := ⟨Subtype.val, Subtype.val_injective⟩
  let S : Finset (Subgroup H0) := c.support.map e
  have hpre_exists :
      ∀ {J : Subgroup H0}, J ∈ S → ∃ i : {J : Subgroup H0 // P J}, i ∈ c.support ∧ i.1 = J := by
    intro J hJ
    rcases Finset.mem_map.1 hJ with ⟨i, hi, hiJ⟩
    exact ⟨i, hi, hiJ⟩
  let preimageOfMem : ∀ J : Subgroup H0, J ∈ S → {J : Subgroup H0 // P J} :=
    fun J hJ ↦ Classical.choose (hpre_exists hJ)
  have hpre_mem :
      ∀ {J : Subgroup H0} (hJ : J ∈ S), preimageOfMem J hJ ∈ c.support := by
    intro J hJ
    exact (Classical.choose_spec (hpre_exists hJ)).1
  have hpre_val :
      ∀ {J : Subgroup H0} (hJ : J ∈ S), (preimageOfMem J hJ).1 = J := by
    intro J hJ
    exact (Classical.choose_spec (hpre_exists hJ)).2
  let a : Subgroup H0 → ℤ := fun J ↦ if hJ : J ∈ S then c (preimageOfMem J hJ) else 0
  refine ⟨S, a, ?_, ?_⟩
  · intro J hJ
    -- Membership in the mapped support remembers the original subgroup proof `P J`.
    exact hpre_val hJ ▸ (preimageOfMem J hJ).2
  · have hsum :
        ∑ J ∈ S, a J • v J = ∑ i ∈ c.support, c i • v i.1 := by
      refine Finset.sum_bij (fun J hJ ↦ preimageOfMem J hJ) ?_ ?_ ?_ ?_
      · intro J hJ
        exact hpre_mem hJ
      · intro J₁ hJ₁ J₂ hJ₂ hEq
        rw [← hpre_val hJ₁, ← hpre_val hJ₂]
        exact congrArg Subtype.val hEq
      · intro i hi
        refine ⟨i.1, Finset.mem_map.2 ⟨i, hi, rfl⟩, ?_⟩
        -- The support map is injective, so the chosen preimage of `i.1` is exactly `i`.
        apply Subtype.ext
        simpa using hpre_val (J := i.1) (Finset.mem_map.2 ⟨i, hi, rfl⟩)
      · intro J hJ
        -- The chosen preimage has the same ambient subgroup, so the summand only changes notation.
        simp [a, hJ, hpre_val hJ]
    -- Replace the finitely supported sum by the ambient subgroup-indexed finite sum.
    calc
      c.sum (fun i n ↦ n • v i.1) = ∑ i ∈ c.support, c i • v i.1 := by
        simp [Finsupp.sum]
      _ = ∑ J ∈ S, a J • v J := hsum.symm

/-- Helper for Remark 11-11.1-3: once the cyclic top-layer scalar is known to lie in the span of
the paired induced-trivial contributions from proper overgroups of the kernel, it can be packaged
in the exact finite interval form used by the pairing theorem. -/
theorem exists_overgroup_finset_sum_of_mem_span_pairings
    {H0 : Type} [Group H0] [Finite H0]
    (β : H0 →* ℂˣ) (ξ : R(H0)) {z : ℂ}
    (hz :
      z ∈ Submodule.span ℤ
        (Set.range fun J : {J : Subgroup H0 // β.ker ≤ J ∧ J < ⊤} ↦
          ⟪(Subgroup.characterRingInduction J.1 (1 : R(J.1)) : H0 → ℂ), (ξ : H0 → ℂ)⟫)) :
    ∃ (S : Finset (Subgroup H0)) (a : Subgroup H0 → ℤ),
      (∀ J ∈ S, β.ker ≤ J ∧ J < ⊤) ∧
        z = ∑ J ∈ S,
          algebraMap ℤ ℂ (a J) *
            ⟪(Subgroup.characterRingInduction J (1 : R(J)) : H0 → ℂ), (ξ : H0 → ℂ)⟫ := by
  obtain ⟨c, hc⟩ :=
    exists_finsupp_eq_sum_of_mem_span_range
      (v := fun J : {J : Subgroup H0 // β.ker ≤ J ∧ J < ⊤} ↦
        ⟪(Subgroup.characterRingInduction J.1 (1 : R(J.1)) : H0 → ℂ), (ξ : H0 → ℂ)⟫) hz
  obtain ⟨S, a, hS, ha⟩ :=
    subgroup_finsupp_sum_eq_finset_sum
      (v := fun J : Subgroup H0 ↦
        (⟪(Subgroup.characterRingInduction J (1 : R(J)) : H0 → ℂ), (ξ : H0 → ℂ)⟫ : ℂ)) c
  refine ⟨S, a, hS, ?_⟩
  -- The new helpers separate the unresolved scalar span membership from the routine finite-support
  -- packaging demanded by the target theorem.
  calc
    z =
        c.sum
          (fun i n ↦ n • ⟪(Subgroup.characterRingInduction i.1 (1 : R(i.1)) : H0 → ℂ),
            (ξ : H0 → ℂ)⟫) := hc
    _ =
        ∑ J ∈ S,
          a J • (⟪(Subgroup.characterRingInduction J (1 : R(J)) : H0 → ℂ),
            (ξ : H0 → ℂ)⟫ : ℂ) := ha
    _ =
        ∑ J ∈ S,
          algebraMap ℤ ℂ (a J) *
            ⟪(Subgroup.characterRingInduction J (1 : R(J)) : H0 → ℂ), (ξ : H0 → ℂ)⟫ := by
          refine Finset.sum_congr rfl ?_
          intro J hJ
          simp [zsmul_eq_mul]

/-- Helper for Remark 11-11.1-3: transporting a proper quotient subgroup `L < ⊤` of
`H.1 ⧸ β.ker` back along the quotient map produces a proper overgroup of `β.ker`, so the
ambient proper-branch divisibility theorem applies directly to its induced trivial pairing. -/
theorem proper_quotient_induced_trivial_pairing_divisible_of_local_proper_branch
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
    (L : Subgroup (H.1 ⧸ β.ker)) (hL : L < ⊤) :
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
    let J : Subgroup H.1 := Subgroup.comap (QuotientGroup.mk' β.ker) L
    ∃ bL : ℤ,
      ⟪(Subgroup.characterRingInduction J (1 : R(J)) : H.1 → ℂ), (ξH : H.1 → ℂ)⟫ =
        algebraMap ℤ ℂ (n * bL) := by
  classical
  dsimp
  obtain ⟨_, hJlt⟩ :=
    quotient_subgroup_comap_above_kernel_and_lt_top β.ker L hL
  -- The quotient subgroup bookkeeping is now finished: the pullback subgroup is proper in `H.1`,
  -- so the previously established proper-branch arithmetic closes the pairing.
  simpa using
    proper_induced_trivial_pairing_divisible_of_local_proper_branch
      X hXelem hdx H sH hsH hproper (Subgroup.comap (QuotientGroup.mk' β.ker) L) hJlt

/-- Helper for Remark 11-11.1-3: pull a quotient-side character-ring element back along the
kernel quotient and pair it against the fixed ambient test character. -/
noncomputable def quotient_pullback_pairing_linearMap
    {H0 : Type} [Group H0] [Finite H0]
    (β : H0 →* ℂˣ) (ξ : R(H0)) :
    R(H0 ⧸ β.ker) →ₗ[ℤ] ℂ :=
  { toFun := fun η ↦
      ⟪(fun x : H0 ↦ ((η : H0 ⧸ β.ker → ℂ) (QuotientGroup.mk' β.ker x))), (ξ : H0 → ℂ)⟫
    map_add' := by
      intro η θ
      -- The pullback pairing is additive because the pairing is additive in its left slot.
      have h := Representation.groupFunctionPairing_add_left
        (fun x : H0 ↦ ((η : H0 ⧸ β.ker → ℂ) (QuotientGroup.mk' β.ker x)))
        (fun x : H0 ↦ ((θ : H0 ⧸ β.ker → ℂ) (QuotientGroup.mk' β.ker x)))
        (ξ : H0 → ℂ)
      simpa using h
    map_smul' := by
      intro a η
      -- The same pullback pairing is `ℤ`-linear in its left slot.
      simpa [zsmul_eq_mul] using
        (Representation.groupFunctionPairing_smul_left
          (a := (a : ℂ))
          (φ := fun x : H0 ↦ ((η : H0 ⧸ β.ker → ℂ) (QuotientGroup.mk' β.ker x)))
          (ψ := (ξ : H0 → ℂ))) }

/-- Helper for Remark 11-11.1-3: the quotient pullback pairing sends the quotient trivial
character to the ambient trivial-line pairing. -/
theorem quotient_pullback_pairing_linearMap_one
    {H0 : Type} [Group H0] [Finite H0]
    (β : H0 →* ℂˣ) (ξ : R(H0)) :
    quotient_pullback_pairing_linearMap β ξ (1 : R(H0 ⧸ β.ker)) =
      ⟪((1 : R(H0)) : H0 → ℂ), (ξ : H0 → ℂ)⟫ := by
  -- Pulling back the quotient unit character along `mk'` leaves the constant-one function.
  simp only [quotient_pullback_pairing_linearMap, LinearMap.coe_mk, AddHom.coe_mk]
  all_goals congr 1
  all_goals funext x
  all_goals simp

/-- Helper for Remark 11-11.1-3: evaluating the quotient pullback pairing on a quotient
linear-character difference gives exactly the ambient erased-difference term. -/
theorem quotient_pullback_pairing_linearMap_difference
    {H0 : Type} [Group H0] [Finite H0]
    (β : H0 →* ℂˣ) (ξ : R(H0))
    (γ : (H0 ⧸ β.ker) →* ℂˣ) :
    quotient_pullback_pairing_linearMap β ξ (γ.toCharacterRing - 1) =
      ⟪(((γ.comp (QuotientGroup.mk' β.ker)).toCharacterRing - 1 : R(H0)) : H0 → ℂ),
          (ξ : H0 → ℂ)⟫ := by
  -- Expanding the pullback definition turns the quotient-side generator into the ambient erased
  -- quotient-character difference term used throughout the kernel recursion.
  simp only [quotient_pullback_pairing_linearMap, LinearMap.coe_mk, AddHom.coe_mk]
  all_goals congr 1
  all_goals funext x
  all_goals simp [MonoidHom.toCharacterRing_apply]

/-- Helper for Remark 11-11.1-3: pulling the quotient induced trivial character back along the
kernel quotient agrees pointwise with induction from the comap subgroup upstairs. -/
theorem quotient_induced_trivial_pullback_eq_comap_induction
    {H0 : Type} [Group H0] [Finite H0]
    (β : H0 →* ℂˣ)
    (L : Subgroup (H0 ⧸ β.ker)) :
    (fun x : H0 ↦
        ((Subgroup.characterRingInduction L (1 : R(L)) : R(H0 ⧸ β.ker)) :
          H0 ⧸ β.ker → ℂ) (QuotientGroup.mk' β.ker x)) =
      (Subgroup.characterRingInduction
          (Subgroup.comap (QuotientGroup.mk' β.ker) L)
          (1 : R(Subgroup.comap (QuotientGroup.mk' β.ker) L)) : H0 → ℂ) := by
  classical
  let e : H0 ⧸ β.ker ≃* β.range := QuotientGroup.quotientKerEquivRange β
  letI : CommGroup (H0 ⧸ β.ker) :=
    { QuotientGroup.Quotient.group β.ker with
      mul_comm := by
        intro a b
        apply e.injective
        simp [mul_comm] }
  let J : Subgroup H0 := Subgroup.comap (QuotientGroup.mk' β.ker) L
  have hindex : (J.index : ℂ) = (L.index : ℂ) := by
    have hcard :
        Fintype.card (H0 ⧸ J) = Fintype.card ((H0 ⧸ β.ker) ⧸ L) := by
      exact
        Fintype.card_congr
          (Representation.quotient_comap_leftCosetEquiv_local
            (Q := H0) (N := β.ker) L)
    -- The quotient-coset equivalence identifies the two subgroup indices.
    simpa [J, Subgroup.index_eq_card] using congrArg (fun n : ℕ ↦ (n : ℂ)) hcard
  ext x
  have hmk :
      QuotientGroup.mk' L (QuotientGroup.mk' β.ker x) = 1 ↔ QuotientGroup.mk' J x = 1 := by
    constructor
    · intro hx
      apply (Subgroup.quotient_mk'_eq_one_iff J x).2
      -- Triviality downstairs is exactly membership in the comap subgroup upstairs.
      change QuotientGroup.mk' β.ker x ∈ L
      exact (Subgroup.quotient_mk'_eq_one_iff L (QuotientGroup.mk' β.ker x)).1 hx
    · intro hx
      apply (Subgroup.quotient_mk'_eq_one_iff L (QuotientGroup.mk' β.ker x)).2
      -- Conversely, membership in the comap subgroup is the defining pullback condition.
      have hxJ : x ∈ J := (Subgroup.quotient_mk'_eq_one_iff J x).1 hx
      simpa [J] using hxJ
  rw [Subgroup.induced_trivial_apply_eq_ite_index_zero (H := L)
      (g := QuotientGroup.mk' β.ker x)]
  rw [Subgroup.induced_trivial_apply_eq_ite_index_zero (H := J) (g := x)]
  by_cases hx : QuotientGroup.mk' J x = 1
  · have hxL : QuotientGroup.mk' L (QuotientGroup.mk' β.ker x) = 1 := (hmk).2 hx
    -- In the fixed-point case, both induced trivial characters take the common index value.
    rw [if_pos hxL, if_pos hx]
    exact hindex.symm
  · have hxL : QuotientGroup.mk' L (QuotientGroup.mk' β.ker x) ≠ 1 := by
      intro hxL
      exact hx ((hmk).1 hxL)
    -- Away from the pulled-back subgroup, both induced trivial characters vanish.
    rw [if_neg hxL, if_neg hx]

/-- Helper for Remark 11-11.1-3: pulling the quotient induced trivial character back along the
kernel quotient identifies it with induction from the comap subgroup upstairs. -/
theorem quotient_pullback_pairing_linearMap_induced_trivial
    {H0 : Type} [Group H0] [Finite H0]
    (β : H0 →* ℂˣ) (ξ : R(H0))
    (L : Subgroup (H0 ⧸ β.ker)) :
    quotient_pullback_pairing_linearMap β ξ (Subgroup.characterRingInduction L (1 : R(L))) =
      ⟪(Subgroup.characterRingInduction
            (Subgroup.comap (QuotientGroup.mk' β.ker) L)
            (1 : R(Subgroup.comap (QuotientGroup.mk' β.ker) L)) : H0 → ℂ),
          (ξ : H0 → ℂ)⟫ := by
  -- Apply the pairing functional to the pointwise pullback/comap identification proved above.
  simpa [quotient_pullback_pairing_linearMap] using
    congrArg
      (fun φ : H0 → ℂ ↦ ⟪φ, (ξ : H0 → ℂ)⟫)
      (quotient_induced_trivial_pullback_eq_comap_induction β L)

/-- Helper for Remark 11-11.1-3: a span relation among quotient pullback pairings over proper
quotient subgroups can be repackaged as an explicit finite `ℤ`-linear combination. -/
theorem quotient_pairing_span_to_finset_sum
    {H0 : Type} [Group H0] [Finite H0]
    (β : H0 →* ℂˣ) (ξ : R(H0)) {z : ℂ}
    (hz :
      z ∈ Submodule.span ℤ
        (Set.range fun L : {L : Subgroup (H0 ⧸ β.ker) // L < ⊤} ↦
          quotient_pullback_pairing_linearMap β ξ
            (Subgroup.characterRingInduction L.1 (1 : R(L.1))))) :
    ∃ S : Finset (Subgroup (H0 ⧸ β.ker)), ∃ a : Subgroup (H0 ⧸ β.ker) → ℤ,
      (∀ L ∈ S, L < ⊤) ∧
      z = ∑ L ∈ S,
        algebraMap ℤ ℂ (a L) *
          quotient_pullback_pairing_linearMap β ξ
            (Subgroup.characterRingInduction L (1 : R(L))) := by
  obtain ⟨c, hc⟩ :=
    exists_finsupp_eq_sum_of_mem_span_range
      (v := fun L : {L : Subgroup (H0 ⧸ β.ker) // L < ⊤} ↦
        quotient_pullback_pairing_linearMap β ξ
          (Subgroup.characterRingInduction L.1 (1 : R(L.1)))) hz
  obtain ⟨S, a, hS, ha⟩ :=
    subgroup_finsupp_sum_eq_finset_sum
      (v := fun L : Subgroup (H0 ⧸ β.ker) ↦
        (quotient_pullback_pairing_linearMap β ξ
          (Subgroup.characterRingInduction L (1 : R(L))) : ℂ)) c
  refine ⟨S, a, hS, ?_⟩
  -- Repackage the finitely supported span witness as the concrete finite sum needed later.
  calc
    z =
        c.sum
          (fun i n ↦ n •
            quotient_pullback_pairing_linearMap β ξ
              (Subgroup.characterRingInduction i.1 (1 : R(i.1)))) := hc
    _ =
        ∑ L ∈ S,
          a L •
            (quotient_pullback_pairing_linearMap β ξ
              (Subgroup.characterRingInduction L (1 : R(L))) : ℂ) := ha
    _ =
        ∑ L ∈ S,
          algebraMap ℤ ℂ (a L) *
            quotient_pullback_pairing_linearMap β ξ
              (Subgroup.characterRingInduction L (1 : R(L))) := by
          refine Finset.sum_congr rfl ?_
          intro L hL
          simp [zsmul_eq_mul]

/-- Helper for Remark 11-11.1-3: applying the quotient pullback pairing to the Chapter 10 cyclic
quotient identity rewrites an induced trivial quotient character as the index-scaled trivial line
plus the full quotient-character difference family. -/
theorem quotient_pullback_pairing_induced_trivial_eq_index_trivial_add_difference_sum
    {H0 : Type} [Group H0] [Finite H0]
    (β : H0 →* ℂˣ) (ξ : R(H0))
    (M : Subgroup (H0 ⧸ β.ker)) [M.Normal]
    (hcomm : ∀ a b : (H0 ⧸ β.ker) ⧸ M, a * b = b * a)
    [Fintype (((H0 ⧸ β.ker) ⧸ M) →* ℂˣ)] :
    quotient_pullback_pairing_linearMap β ξ
      (Subgroup.characterRingInduction M (1 : R(M))) =
      (M.index : ℂ) * quotient_pullback_pairing_linearMap β ξ (1 : R(H0 ⧸ β.ker)) +
        ∑ δ : ((H0 ⧸ β.ker) ⧸ M) →* ℂˣ,
          quotient_pullback_pairing_linearMap β ξ
            (((δ.comp (QuotientGroup.mk' M)).toCharacterRing - 1 : R(H0 ⧸ β.ker))) := by
  have hrewrite :
      quotient_pullback_pairing_linearMap β ξ
        (Subgroup.characterRingInduction M (1 : R(M))) -
          (M.index : ℂ) * quotient_pullback_pairing_linearMap β ξ (1 : R(H0 ⧸ β.ker)) =
        ∑ δ : ((H0 ⧸ β.ker) ⧸ M) →* ℂˣ,
          quotient_pullback_pairing_linearMap β ξ
            (((δ.comp (QuotientGroup.mk' M)).toCharacterRing - 1 : R(H0 ⧸ β.ker))) := by
    -- Apply the quotient pullback linear functional directly to the quotient-character identity.
    have h := congrArg
      (quotient_pullback_pairing_linearMap β ξ)
      (induced_trivial_sub_index_smul_one_eq_sum_quotient_linearCharacter_differences
        (G := H0 ⧸ β.ker) (H := M) hcomm)
    rw [map_sub, map_zsmul, map_sum] at h
    simpa [zsmul_eq_mul] using h
  -- Move the scaled trivial-line term to the right so later arguments can split the quotient
  -- character family by kernel type.
  exact (sub_eq_iff_eq_add.1 hrewrite).trans <| by
    simp [add_comm, add_left_comm, add_assoc]

/-- Helper for Remark 11-11.1-3: after isolating a nontrivial quotient character on the kernel
quotient, the quotient pullback pairing sees its kernel-induced trivial character as the
index-scaled trivial line, the distinguished difference term, and the remaining erased branch. -/
theorem quotient_pullback_pairing_kernel_induced_decomposes_with_distinguished_difference
    {H0 : Type} [Group H0] [Finite H0]
    (β : H0 →* ℂˣ) (ξ : R(H0))
    (γ : (H0 ⧸ β.ker) →* ℂˣ) (hγ : γ ≠ 1) :
    let γq : ((H0 ⧸ β.ker) ⧸ γ.ker) →* ℂˣ :=
      QuotientGroup.lift γ.ker γ (show γ.ker ≤ γ.ker from le_rfl)
    quotient_pullback_pairing_linearMap β ξ
      (Subgroup.characterRingInduction γ.ker (1 : R(γ.ker))) =
      (γ.ker.index : ℂ) * quotient_pullback_pairing_linearMap β ξ (1 : R(H0 ⧸ β.ker)) +
        quotient_pullback_pairing_linearMap β ξ (γ.toCharacterRing - 1) +
          ∑ δ ∈ Finset.univ.erase γq,
            quotient_pullback_pairing_linearMap β ξ
              (((δ.comp (QuotientGroup.mk' γ.ker)).toCharacterRing - 1 :
                  R((H0 ⧸ β.ker)))) := by
  classical
  dsimp
  obtain ⟨hγ_factor, hγq_ne, _, hcomm⟩ :=
    kernel_quotient_distinguished_character_data (H0 := H0 ⧸ β.ker) γ hγ
  letI : CommGroup (((H0 ⧸ β.ker) ⧸ γ.ker)) :=
    { QuotientGroup.Quotient.group γ.ker with
      mul_comm := hcomm }
  letI : Fintype ((((H0 ⧸ β.ker) ⧸ γ.ker) →* ℂˣ)) := linearCharacterFintype
  let γq : ((H0 ⧸ β.ker) ⧸ γ.ker) →* ℂˣ :=
    QuotientGroup.lift γ.ker γ (show γ.ker ≤ γ.ker from le_rfl)
  let term : (((H0 ⧸ β.ker) ⧸ γ.ker) →* ℂˣ) → ℂ := fun δ ↦
    quotient_pullback_pairing_linearMap β ξ
      (((δ.comp (QuotientGroup.mk' γ.ker)).toCharacterRing - 1 : R((H0 ⧸ β.ker))))
  have hsplit :
      ∑ δ : ((H0 ⧸ β.ker) ⧸ γ.ker) →* ℂˣ, term δ =
        term γq + ∑ δ ∈ Finset.univ.erase γq, term δ := by
    -- Isolate the distinguished quotient character from the full quotient-character family.
    simpa [term, add_comm] using
      (Finset.sum_erase_add Finset.univ term (Finset.mem_univ γq)).symm
  have hγq_term :
      term γq =
        quotient_pullback_pairing_linearMap β ξ (γ.toCharacterRing - 1) := by
    -- The distinguished quotient character recovers `γ` after precomposing with the quotient map.
    rw [show γ.toCharacterRing = (γq.comp (QuotientGroup.mk' γ.ker)).toCharacterRing from
      congrArg MonoidHom.toCharacterRing hγ_factor]
  -- Apply the previous quotient-side identity and then split off the distinguished quotient
  -- character from the remaining family.
  calc
    quotient_pullback_pairing_linearMap β ξ
        (Subgroup.characterRingInduction γ.ker (1 : R(γ.ker))) =
      (γ.ker.index : ℂ) * quotient_pullback_pairing_linearMap β ξ (1 : R(H0 ⧸ β.ker)) +
        ∑ δ : ((H0 ⧸ β.ker) ⧸ γ.ker) →* ℂˣ, term δ := by
          simpa [term] using
            quotient_pullback_pairing_induced_trivial_eq_index_trivial_add_difference_sum
              (β := β) (ξ := ξ) (M := γ.ker) hcomm
    _ =
      (γ.ker.index : ℂ) * quotient_pullback_pairing_linearMap β ξ (1 : R(H0 ⧸ β.ker)) +
        (term γq + ∑ δ ∈ Finset.univ.erase γq, term δ) := by
          rw [hsplit]
    _ =
      (γ.ker.index : ℂ) * quotient_pullback_pairing_linearMap β ξ (1 : R(H0 ⧸ β.ker)) +
        quotient_pullback_pairing_linearMap β ξ (γ.toCharacterRing - 1) +
          ∑ δ ∈ Finset.univ.erase γq, term δ := by
            simpa [hγq_term, add_assoc]

/-- Helper for Remark 11-11.1-3: the cyclic quotient top layer belongs to the `ℤ`-span generated
by the induced trivial pairings coming from proper overgroups of the kernel. This is the exact
source-faithful bridge needed before packaging the top layer as a finite overgroup sum. -/
theorem faithful_quotient_top_layer_eq_quotient_pullback_pairing
    {H0 : Type} [Group H0] [Finite H0]
    (β : H0 →* ℂˣ) (ξ : R(H0)) :
    let βq : (H0 ⧸ β.ker) →* ℂˣ :=
      QuotientGroup.lift β.ker β (show β.ker ≤ β.ker from le_rfl)
    let term : ((H0 ⧸ β.ker) →* ℂˣ) → ℂ := fun γ ↦
      ⟪(((γ.comp (QuotientGroup.mk' β.ker)).toCharacterRing - 1 : R(H0)) :
            H0 → ℂ),
          (ξ : H0 → ℂ)⟫
    let η : R(H0 ⧸ β.ker) :=
      (β.ker.index : ℤ) • (1 : R(H0 ⧸ β.ker)) +
        ∑ γ ∈ ((Finset.univ.erase βq).filter fun γ => γ.ker = ⊥),
          ((γ.toCharacterRing - 1 : R(H0 ⧸ β.ker)))
    (β.ker.index : ℂ) * ⟪((1 : R(H0)) : H0 → ℂ), (ξ : H0 → ℂ)⟫ +
        ∑ γ ∈ ((Finset.univ.erase βq).filter fun γ => γ.ker = ⊥), term γ =
      quotient_pullback_pairing_linearMap β ξ η := by
  classical
  dsimp
  let βq : (H0 ⧸ β.ker) →* ℂˣ :=
    QuotientGroup.lift β.ker β (show β.ker ≤ β.ker from le_rfl)
  let term : ((H0 ⧸ β.ker) →* ℂˣ) → ℂ := fun γ ↦
    ⟪(((γ.comp (QuotientGroup.mk' β.ker)).toCharacterRing - 1 : R(H0)) :
          H0 → ℂ),
        (ξ : H0 → ℂ)⟫
  have hone :
      quotient_pullback_pairing_linearMap β ξ ((β.ker.index : ℤ) • (1 : R(H0 ⧸ β.ker))) =
        (β.ker.index : ℂ) * ⟪((1 : R(H0)) : H0 → ℂ), (ξ : H0 → ℂ)⟫ := by
    -- Rewrite the index-scaled quotient trivial character by linearity and then pull it back.
    calc
      quotient_pullback_pairing_linearMap β ξ ((β.ker.index : ℤ) • (1 : R(H0 ⧸ β.ker))) =
          (β.ker.index : ℤ) • quotient_pullback_pairing_linearMap β ξ (1 : R(H0 ⧸ β.ker)) := by
            exact map_zsmul (quotient_pullback_pairing_linearMap β ξ) _ _
      _ = (β.ker.index : ℤ) • ⟪((1 : R(H0)) : H0 → ℂ), (ξ : H0 → ℂ)⟫ := by
            rw [quotient_pullback_pairing_linearMap_one]
      _ = (β.ker.index : ℂ) * ⟪((1 : R(H0)) : H0 → ℂ), (ξ : H0 → ℂ)⟫ := by
            simp [zsmul_eq_mul, Int.cast_natCast]
  have hsum :
      quotient_pullback_pairing_linearMap β ξ
          (∑ γ ∈ ((Finset.univ.erase βq).filter fun γ => γ.ker = ⊥),
            ((γ.toCharacterRing - 1 : R(H0 ⧸ β.ker)))) =
        ∑ γ ∈ ((Finset.univ.erase βq).filter fun γ => γ.ker = ⊥), term γ := by
    -- Each faithful erased quotient-character difference pulls back to the ambient erased term.
    rw [map_sum]
    refine Finset.sum_congr rfl fun γ _ ↦ ?_
    exact quotient_pullback_pairing_linearMap_difference β ξ γ
  -- The whole top layer is the pullback pairing applied to the quotient-side faithful package.
  calc
    (β.ker.index : ℂ) * ⟪((1 : R(H0)) : H0 → ℂ), (ξ : H0 → ℂ)⟫ +
        ∑ γ ∈ ((Finset.univ.erase βq).filter fun γ => γ.ker = ⊥), term γ =
      quotient_pullback_pairing_linearMap β ξ ((β.ker.index : ℤ) • (1 : R(H0 ⧸ β.ker))) +
        quotient_pullback_pairing_linearMap β ξ
          (∑ γ ∈ ((Finset.univ.erase βq).filter fun γ => γ.ker = ⊥),
            ((γ.toCharacterRing - 1 : R(H0 ⧸ β.ker)))) := by
              rw [← hone, ← hsum]
    _ =
      quotient_pullback_pairing_linearMap β ξ
        ((β.ker.index : ℤ) • (1 : R(H0 ⧸ β.ker)) +
          ∑ γ ∈ ((Finset.univ.erase βq).filter fun γ => γ.ker = ⊥),
            ((γ.toCharacterRing - 1 : R(H0 ⧸ β.ker)))) := by
              simp

/-- Helper for Remark 11-11.1-3: once the quotient-side faithful top layer itself has pairing
divisible by `n`, the displayed faithful cyclic-layer scalar on the ambient group has the same
divisibility. -/
theorem faithful_quotient_top_layer_divisible_of_pullback_divisible
    {H0 : Type} [Group H0] [Finite H0] {n : ℤ}
    (β : H0 →* ℂˣ) (ξ : R(H0))
    (hdiv :
      let βq : (H0 ⧸ β.ker) →* ℂˣ :=
        QuotientGroup.lift β.ker β (show β.ker ≤ β.ker from le_rfl)
      let η : R(H0 ⧸ β.ker) :=
        (β.ker.index : ℤ) • (1 : R(H0 ⧸ β.ker)) +
          ∑ γ ∈ ((Finset.univ.erase βq).filter fun γ => γ.ker = ⊥),
            ((γ.toCharacterRing - 1 : R(H0 ⧸ β.ker)))
      ∃ b : ℤ, quotient_pullback_pairing_linearMap β ξ η = algebraMap ℤ ℂ (n * b)) :
    ∃ b : ℤ,
      (β.ker.index : ℂ) * ⟪((1 : R(H0)) : H0 → ℂ), (ξ : H0 → ℂ)⟫ +
        ∑ γ ∈ ((Finset.univ.erase
            (QuotientGroup.lift β.ker β (show β.ker ≤ β.ker from le_rfl))).filter
          fun γ => γ.ker = ⊥),
          ⟪(((γ.comp (QuotientGroup.mk' β.ker)).toCharacterRing - 1 : R(H0)) :
                H0 → ℂ),
              (ξ : H0 → ℂ)⟫ =
        algebraMap ℤ ℂ (n * b) := by
  classical
  dsimp at hdiv ⊢
  rcases hdiv with ⟨b, hb⟩
  refine ⟨b, ?_⟩
  -- Rewrite the ambient faithful layer back to the quotient-pullback pairing, then use the
  -- packaged quotient-side divisibility witness unchanged.
  calc
    (β.ker.index : ℂ) * ⟪((1 : R(H0)) : H0 → ℂ), (ξ : H0 → ℂ)⟫ +
        ∑ γ ∈ ((Finset.univ.erase
            (QuotientGroup.lift β.ker β (show β.ker ≤ β.ker from le_rfl))).filter
          fun γ => γ.ker = ⊥),
          ⟪(((γ.comp (QuotientGroup.mk' β.ker)).toCharacterRing - 1 : R(H0)) :
                H0 → ℂ),
              (ξ : H0 → ℂ)⟫ =
      quotient_pullback_pairing_linearMap β ξ
        ((β.ker.index : ℤ) • (1 : R(H0 ⧸ β.ker)) +
          ∑ γ ∈ ((Finset.univ.erase
              (QuotientGroup.lift β.ker β (show β.ker ≤ β.ker from le_rfl))).filter
            fun γ => γ.ker = ⊥),
            ((γ.toCharacterRing - 1 : R(H0 ⧸ β.ker)))) := by
          simpa using faithful_quotient_top_layer_eq_quotient_pullback_pairing (β := β) (ξ := ξ)
    _ = algebraMap ℤ ℂ (n * b) := hb


end CharacterizationOfCharacters

end Representation
