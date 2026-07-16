import LinearRepresentations_Serre_1977.Serre.Chap10.Exercise_10_10_5_5.BrauerPrelude

noncomputable section

universe u

open scoped Representation SubgroupInduction

namespace Representation

section

variable {G : Type} [Group G] [Finite G]

private noncomputable abbrev finiteGroupFintype : Fintype G := Fintype.ofFinite G
attribute [local instance] finiteGroupFintype

/-- A subgroup of a finite group is finite. -/
private noncomputable abbrev subgroupFintype (H : Subgroup G) : Fintype H := Fintype.ofFinite H
attribute [local instance] subgroupFintype

attribute [local instance] Representation.quotientFintype

/-- Helper for Exercise 10-10.5-5: elementary groups stay elementary under group isomorphisms. -/
lemma isElementary_of_mulEquiv
    {H : Type*} [Group H] {J : Type*} [Group J]
    (e : H ≃* J) (hH : IsElementary H) :
    IsElementary J := by
  rcases hH with ⟨p, C, P, hCP⟩
  -- Transport the textbook `p`-elementary decomposition across the given group equivalence.
  letI : Finite H := (show IsPElementary p H from ⟨C, P, hCP⟩).finite
  letI : Finite P := hCP.finite_pGroup_factor
  letI : Finite J := Finite.of_equiv H e.toEquiv
  letI : IsCyclic C := hCP.cyclic
  refine ⟨p, C.map e.toMonoidHom, P.map e.toMonoidHom, ?_⟩
  refine ⟨hCP.prime, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact Finite.of_equiv P (Subgroup.equivMapOfInjective P e.toMonoidHom e.injective)
  · let eC : C ≃* C.map e.toMonoidHom := Subgroup.equivMapOfInjective C e.toMonoidHom e.injective
    exact isCyclic_of_surjective eC eC.surjective
  · have hcard : Nat.card (C.map e.toMonoidHom) = Nat.card C :=
      (Nat.card_congr (Subgroup.equivMapOfInjective C e.toMonoidHom e.injective).toEquiv).symm
    exact hcard ▸ hCP.coprime_card
  · exact hCP.isPGroup.of_equiv (Subgroup.equivMapOfInjective P e.toMonoidHom e.injective)
  · intro c hc y hy
    rcases hc with ⟨c0, hc0, rfl⟩
    rcases hy with ⟨y0, hy0, rfl⟩
    simpa using congrArg e (hCP.centralizes hc0 y0 hy0)
  · have hcardC : Nat.card (C.map e.toMonoidHom) = Nat.card C :=
        (Nat.card_congr (Subgroup.equivMapOfInjective C e.toMonoidHom e.injective).toEquiv).symm
    have hcardP : Nat.card (P.map e.toMonoidHom) = Nat.card P :=
        (Nat.card_congr (Subgroup.equivMapOfInjective P e.toMonoidHom e.injective).toEquiv).symm
    have hcardJ : Nat.card H = Nat.card J := Nat.card_congr e.toEquiv
    refine Subgroup.isComplement'_of_card_mul_and_disjoint ?_ ?_
    · calc
        Nat.card (C.map e.toMonoidHom) * Nat.card (P.map e.toMonoidHom)
            = Nat.card C * Nat.card P := by rw [hcardC, hcardP]
        _ = Nat.card H := hCP.isComplement.card_mul
        _ = Nat.card J := hcardJ
    · rw [disjoint_iff, ← Subgroup.map_inf C P e.toMonoidHom e.injective,
        disjoint_iff.mp hCP.isComplement.disjoint, Subgroup.map_bot]

/-- Helper for Exercise 10-10.5-5: inducing a degree-`1` character from the top subgroup recovers
the same degree-`1` character on the ambient group. -/
theorem characterRingInduction_top_toCharacterRing
    (β : G →* ℂˣ) :
    Subgroup.characterRingInduction (⊤ : Subgroup G)
      ((β.comp Subgroup.topEquiv.toMonoidHom).toCharacterRing : R((⊤ : Subgroup G))) =
        (β.toCharacterRing : R(G)) := by
  -- On the full subgroup, the induced class-function formula averages a conjugacy-invariant
  -- function over all conjugates of `g`, so it returns the original linear character.
  ext g
  have hcard_top : Nat.card (⊤ : Subgroup G) = Nat.card G :=
    Nat.card_congr Subgroup.topEquiv.toEquiv
  have hG0 : (Nat.card G : ℂ) ≠ 0 := by
    exact Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  calc
    (((Subgroup.characterRingInduction (⊤ : Subgroup G)
        ((β.comp Subgroup.topEquiv.toMonoidHom).toCharacterRing :
          R((⊤ : Subgroup G))) : R(G)) : G → ℂ) g) =
      ((Nat.card G : ℂ)⁻¹) * ∑ s : G, (β g : ℂ) := by
        rw [Subgroup.characterRingInduction_apply, Subgroup.inducedClassFunction, hcard_top]
        simp [MonoidHom.toCharacterRing_apply, mul_assoc]
    _ = ((Nat.card G : ℂ)⁻¹) * ((Nat.card G : ℂ) * (β g : ℂ)) := by
      simp [nsmul_eq_mul]
    _ = (β g : ℂ) := by
      field_simp [hG0]
    _ = ((β.toCharacterRing : R(G)) : G → ℂ) g := by
      simp [MonoidHom.toCharacterRing_apply]

/-- Helper for Exercise 10-10.5-5: in an elementary ambient group, the difference of a degree-`1`
character from the trivial character already belongs to Serre's augmentation subgroup `R₀'(G)`. -/
theorem linearCharacter_difference_mem_elementaryLinearCharacterAugmentationSpan_of_isElementary
    (hG : IsElementary G) (β : G →* ℂˣ) :
    (β.toCharacterRing - 1 : R(G)) ∈ R₀'(G) := by
  -- Use the generator with `E = ⊤`: after transporting `β` to the top subgroup, induction from
  -- `⊤` gives back the same linear-character difference on `G`.
  refine Submodule.subset_span ?_
  refine ⟨(⊤ : Subgroup G), isElementary_of_mulEquiv Subgroup.topEquiv.symm hG,
    β.comp Subgroup.topEquiv.toMonoidHom, ?_⟩
  have htop_one :
      Subgroup.characterRingInduction (⊤ : Subgroup G) (1 : R((⊤ : Subgroup G))) =
        (1 : R(G)) := by
    ext g
    simp [Subgroup.characterRingInduction_apply, Subgroup.inducedClassFunction]
  symm
  calc
    Subgroup.characterRingInduction (⊤ : Subgroup G)
        (((β.comp Subgroup.topEquiv.toMonoidHom).toCharacterRing :
            R((⊤ : Subgroup G))) - 1) =
      Subgroup.characterRingInduction (⊤ : Subgroup G)
          ((β.comp Subgroup.topEquiv.toMonoidHom).toCharacterRing :
            R((⊤ : Subgroup G))) -
        Subgroup.characterRingInduction (⊤ : Subgroup G) (1 : R((⊤ : Subgroup G))) := by
          rw [(Subgroup.characterRingInduction (⊤ : Subgroup G)).map_sub]
    _ =
      (β.toCharacterRing : R(G)) -
        Subgroup.characterRingInduction (⊤ : Subgroup G) (1 : R((⊤ : Subgroup G))) := by
          rw [characterRingInduction_top_toCharacterRing β]
    _ = β.toCharacterRing - 1 := by
      rw [htop_one]

namespace Subgroup

/-- Helper for Exercise 10-10.5-5: the trivial degree-`1` character gives the trivial element of
Serre's character ring. -/
theorem toCharacterRing_one (H : Subgroup G) :
    ((1 : H →* ℂˣ).toCharacterRing : R(H)) = 1 := by
  -- Both class functions are identically `1`, so the bundled character-ring elements agree.
  ext h
  simp [MonoidHom.toCharacterRing_apply]

/-- Helper for Exercise 10-10.5-5: a subgroup of an elementary finite group is elementary. -/
theorem isElementary_of_isElementary
    (H : Subgroup G) (hG : IsElementary G) :
    IsElementary H := by
  rcases hG with ⟨p, hpG⟩
  rcases hpG with ⟨C, P, hCP⟩
  letI : Fact (Nat.Prime p) := ⟨hCP.prime⟩
  let C' : Subgroup H := (H ⊓ C).subgroupOf H
  let P' : Subgroup H := (H ⊓ P).subgroupOf H
  have hC'card : Nat.card ↥C' = Nat.card ↥(H ⊓ C) := by
    exact Nat.card_congr
      (Subgroup.subgroupOfEquivOfLe (show H ⊓ C ≤ H from inf_le_left)).toEquiv
  -- The `p`-regular and `p`-power components of an element of `H` stay in `H`, so the ambient
  -- `p`-elementary decomposition restricts to `H`.
  refine ⟨p, C', P', ?_⟩
  refine ⟨hCP.prime, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · infer_instance
  · -- The cyclic factor restricts to a cyclic subgroup of `H`.
    letI : IsCyclic ↥C := hCP.cyclic
    letI : IsCyclic ↥(H ⊓ C) :=
      Subgroup.isCyclic_of_le (show H ⊓ C ≤ C from inf_le_right)
    exact
      isCyclic_of_surjective
        (Subgroup.subgroupOfEquivOfLe (show H ⊓ C ≤ H from inf_le_left)).symm.toMonoidHom
        (Subgroup.subgroupOfEquivOfLe (show H ⊓ C ≤ H from inf_le_left)).symm.surjective
  · -- The restricted cyclic factor still has order prime to `p`.
    have hdiv : Nat.card ↥(H ⊓ C) ∣ Nat.card ↥C := by
      exact Subgroup.card_dvd_of_le (show H ⊓ C ≤ C from inf_le_right)
    rw [hC'card]
    exact hCP.coprime_card.of_dvd_right hdiv
  · -- The `p`-group factor restricts along the subgroup inclusion.
    have hPsub : IsPGroup p ↥((H ⊓ P).subgroupOf P) := by
      exact hCP.isPGroup.to_subgroup ((H ⊓ P).subgroupOf P)
    have hPinf_right : IsPGroup p ↥(H ⊓ P) := by
      exact hPsub.of_equiv
        (Subgroup.subgroupOfEquivOfLe (show H ⊓ P ≤ P from inf_le_right))
    exact hPinf_right.of_equiv
      (Subgroup.subgroupOfEquivOfLe (show H ⊓ P ≤ H from inf_le_left)).symm
  · -- Elements in the restricted cyclic factor still centralize the restricted `p`-group factor.
    intro c hc u hu
    have hcC : ((c : H) : G) ∈ C := by
      exact (show ((c : H) : G) ∈ H ⊓ C from hc).2
    have huP : ((u : H) : G) ∈ P := by
      exact (show ((u : H) : G) ∈ H ⊓ P from hu).2
    apply Subtype.ext
    simpa using hCP.centralizes hcC ((u : H) : G) huP
  · -- The restricted `p'`- and `p`-parts still multiply to every element of `H`.
    refine Subgroup.isComplement'_of_disjoint_and_mul_eq_univ ?_ ?_
    · rw [Subgroup.disjoint_def]
      intro x hxC hxP
      have hxCG : ((x : H) : G) ∈ C := by
        exact (show ((x : H) : G) ∈ H ⊓ C from hxC).2
      have hxPG : ((x : H) : G) ∈ P := by
        exact (show ((x : H) : G) ∈ H ⊓ P from hxP).2
      have hxbot : ((x : H) : G) ∈ (⊥ : Subgroup G) := by
        have hbot : C ⊓ P = (⊥ : Subgroup G) := disjoint_iff.mp hCP.isComplement.disjoint
        exact hbot ▸ ⟨hxCG, hxPG⟩
      apply Subtype.ext
      simpa using hxbot
    · apply Set.eq_univ_iff_forall.2
      intro x
      let xr : H := pRegularComponent p x
      let xu : H := pUnipotentComponent p x
      have hdecomp :
          IsPComponentDecomposition p x xu xr := by
        simpa [xu, xr] using
          p_component_decomposition_exists (p := p) x (isOfFinOrder_of_finite x)
      have hxrC : (xr : G) ∈ C := by
        have hxrReg : IsPRegular p (xr : G) := by
          simpa [IsPRegular, Subgroup.orderOf_mk, xr] using hdecomp.isPRegular
        change (xr : G) ∈ (C : Set G)
        rw [hCP.cyclic_factor_eq_setOf_isPRegular]
        exact hxrReg
      have hxuP : (xu : G) ∈ P := by
        have hxuElt : IsPElement p (xu : G) := by
          simpa [IsPElement, Subgroup.orderOf_mk, xu] using hdecomp.isPElement
        change (xu : G) ∈ (P : Set G)
        rw [hCP.p_group_factor_eq_setOf_isPElement]
        exact hxuElt
      have hxr_mem : xr ∈ C' := by
        change (xr : G) ∈ H ⊓ C
        exact ⟨xr.2, hxrC⟩
      have hxu_mem : xu ∈ P' := by
        change (xu : G) ∈ H ⊓ P
        exact ⟨xu.2, hxuP⟩
      refine ⟨xr, hxr_mem, xu, hxu_mem, ?_⟩
      calc
        xr * xu = xu * xr := by
          simpa using hdecomp.commute.symm
        _ = x := hdecomp.mul_eq

-- `Subgroup.mappedLinearCharacter` is the canonical declaration from
-- `Serre.Chap10.Theorem_10_10_5_2.BrauerInductionInfrastructure` (transitively imported);
-- reused directly rather than kept as a duplicate copy.

omit [Finite G] in
/-- Helper for Exercise 10-10.5-5: restricting the mapped subgroup `K.map H.subtype` back to `H`
recovers the original subgroup `K`. -/
theorem subgroup_chain_inner_subgroup_eq
    (H : Subgroup G) (K : Subgroup H) :
    ((K.map H.subtype).subgroupOf H : Subgroup H) = K := by
  -- The image subgroup consists exactly of those elements of `H` coming from `K`.
  ext k
  change k.1 ∈ K.map H.subtype ↔ k ∈ K
  constructor
  · intro hk
    rcases hk with ⟨x, hx, hxk⟩
    have : x = k := by
      apply Subtype.ext
      simpa using hxk
    simpa [this] using hx
  · intro hk
    exact ⟨k, hk, rfl⟩

omit [Finite G] in
/-- Helper for Exercise 10-10.5-5: the mapped subgroup `K.map H.subtype` is contained in `H`. -/
theorem subgroup_chain_map_le
    (H : Subgroup G) (K : Subgroup H) :
    K.map H.subtype ≤ H := by
  -- Every element of the mapped subgroup is literally the image of an element of `K ≤ H`.
  intro x hx
  rcases hx with ⟨y, -, rfl⟩
  exact y.property

-- `Subgroup.transport_mappedLinearCharacter_eq_original` is the canonical declaration from
-- `Serre.Chap10.Theorem_10_10_5_2.BrauerInductionInfrastructure` (transitively imported);
-- reused directly rather than kept as a duplicate copy.

-- `Subgroup.inducedClassFunction_subgroupOf_induction_in_stages` and
-- `Subgroup.characterRingInduction_induced_linearCharacter_subgroup_chain` are the canonical
-- declarations from `Serre.Chap10.Theorem_10_10_5_2.BrauerInductionInfrastructure` (transitively
-- imported); reused directly rather than kept as duplicate copies.

/-- Helper for Exercise 10-10.5-5: the transported trivial character on `K.map H.subtype` is
still trivial. -/
theorem mappedLinearCharacter_one
    (H : Subgroup G) (K : Subgroup H) :
    mappedLinearCharacter H K (1 : K →* ℂˣ) = 1 := by
  -- The transported character is computed by precomposing the trivial character with an
  -- equivalence, so it remains identically `1`.
  ext x
  simp [mappedLinearCharacter]

/-- Helper for Exercise 10-10.5-5: inducing a linear-character difference from `K ≤ H ≤ G`
should agree with one-step induction from `K.map H.subtype ≤ G`. -/
theorem characterRingInduction_linear_difference_subgroup_chain
    (H : Subgroup G) (K : Subgroup H) (α : K →* ℂˣ) :
    Subgroup.characterRingInduction H
      (Subgroup.characterRingInduction K (α.toCharacterRing - 1)) =
      Subgroup.characterRingInduction (K.map H.subtype)
        ((mappedLinearCharacter H K α).toCharacterRing - 1) := by
  -- Reduce the difference statement to the honest induction-in-stages statement by linearity and
  -- by identifying the transported trivial character with the trivial character.
  calc
    Subgroup.characterRingInduction H
        (Subgroup.characterRingInduction K (α.toCharacterRing - 1)) =
      Subgroup.characterRingInduction H
        (Subgroup.characterRingInduction K α.toCharacterRing -
          Subgroup.characterRingInduction K (1 : R(K))) := by
      rw [(Subgroup.characterRingInduction K).map_sub]
    _ =
      Subgroup.characterRingInduction H (Subgroup.characterRingInduction K α.toCharacterRing) -
        Subgroup.characterRingInduction H (Subgroup.characterRingInduction K (1 : R(K))) := by
      rw [(Subgroup.characterRingInduction H).map_sub]
    _ =
      Subgroup.characterRingInduction (K.map H.subtype)
          ((mappedLinearCharacter H K α).toCharacterRing) -
        Subgroup.characterRingInduction (K.map H.subtype)
          ((mappedLinearCharacter H K (1 : K →* ℂˣ)).toCharacterRing) := by
      rw [← toCharacterRing_one K]
      rw [characterRingInduction_induced_linearCharacter_subgroup_chain H K α,
        characterRingInduction_induced_linearCharacter_subgroup_chain H K (1 : K →* ℂˣ)]
    _ =
      Subgroup.characterRingInduction (K.map H.subtype)
          ((mappedLinearCharacter H K α).toCharacterRing) -
        Subgroup.characterRingInduction (K.map H.subtype) (1 : R(K.map H.subtype)) := by
      rw [mappedLinearCharacter_one H K, toCharacterRing_one (K.map H.subtype)]
    _ =
      Subgroup.characterRingInduction (K.map H.subtype)
        (((mappedLinearCharacter H K α).toCharacterRing) - 1) := by
      rw [← (Subgroup.characterRingInduction (K.map H.subtype)).map_sub]

-- Proof sketch: each generator of `R₀'(H)` is itself induced from a linear character difference on
-- an elementary subgroup `E ≤ H`; induction in stages rewrites its image in `R(G)` as the same
-- kind of generator coming from the elementary subgroup `E ≤ G`.
/-- Induction from a subgroup sends Serre's augmentation subgroup `R₀'` into `R₀'`. -/
theorem map_elementaryLinearCharacterAugmentationSpan (H : Subgroup G) :
    Submodule.map (Subgroup.characterRingInduction H) (R₀'(H)) ≤ R₀'(G) := by
  -- Reduce the image of the span to its generators, then rewrite each generator by induction in
  -- stages along the subgroup chain `K ≤ H ≤ G`.
  rw [elementaryLinearCharacterAugmentationSpan, Submodule.map_span_le]
  intro χ hχ
  rcases hχ with ⟨K, hK, α, rfl⟩
  refine Submodule.subset_span ?_
  refine ⟨K.map H.subtype, ?_, mappedLinearCharacter H K α, ?_⟩
  · exact isElementary_of_mulEquiv
      (Subgroup.equivMapOfInjective K H.subtype H.subtype_injective) hK
  · simpa using
      characterRingInduction_linear_difference_subgroup_chain H K α

/-- Helper for Exercise 10-10.5-5: if `H` is normal with abelian quotient, the induced trivial
character belongs to Serre's subgroup `R'(G)`. -/
theorem induced_trivial_apply_eq_quotient_regular_value
    (H : Subgroup G) [H.Normal] (g : G) :
    ((Subgroup.characterRingInduction H (1 : R(H)) : R(G)) : G → ℂ) g =
      (leftRegular ℂ (G ⧸ H)).character (QuotientGroup.mk' H g) := by
  let hnormal : H.Normal := inferInstance
  by_cases hg : g ∈ H
  · have hq : QuotientGroup.mk' H g = 1 := by
      simpa using hg
    have hall : ∀ s : G, s⁻¹ * g * s ∈ H := by
      intro s
      exact hnormal.conj_mem' g hg s
    have hH0 : (Nat.card H : ℂ) ≠ 0 := by
      exact Nat.cast_ne_zero.mpr Nat.card_pos.ne'
    have hcard : (Nat.card G : ℂ) = (Nat.card H : ℂ) * H.index := by
      exact_mod_cast H.card_mul_index.symm
    -- When `g ∈ H`, every conjugate lies in `H`, so the induction formula collapses to the index.
    calc
      ((Subgroup.characterRingInduction H (1 : R(H)) : R(G)) : G → ℂ) g
          = ((Nat.card H : ℂ)⁻¹) * (Nat.card G : ℂ) := by
              rw [Subgroup.characterRingInduction_apply, Subgroup.inducedClassFunction]
              simp [hall]
      _ = (H.index : ℂ) := by
        rw [hcard]
        field_simp [hH0]
      _ = (leftRegular ℂ (G ⧸ H)).character (QuotientGroup.mk' H g) := by
        simpa [hq, H.index_eq_card] using
          (Representation.leftRegular_character_one (k := ℂ) (G := G ⧸ H))
  · rw [Subgroup.characterRingInduction_apply]
    have hq : QuotientGroup.mk' H g ≠ 1 := by
      simpa using hg
    have hall : ∀ s : G, s⁻¹ * g * s ∉ H := by
      intro s hs
      apply hg
      simpa [mul_assoc] using hnormal.conj_mem _ hs s
    -- When `g ∉ H`, normality forces every summand in the induction formula to vanish.
    calc
      Ind[H]((1 : H → ℂ)) g = 0 := by
        simp [Subgroup.inducedClassFunction, hall]
      _ = (leftRegular ℂ (G ⧸ H)).character (QuotientGroup.mk' H g) := by
        symm
        exact Representation.leftRegular_character_eq_zero_of_ne_one hq

/-- Helper for Exercise 10-10.5-5: evaluating `Ind_H^G(1)` at `g` only depends on whether the
quotient class `gH` is trivial, and in the trivial case the value is the subgroup index. -/
theorem induced_trivial_apply_eq_ite_index_zero
    (H : Subgroup G) [H.Normal] [DecidableEq (G ⧸ H)] (g : G) :
    ((Subgroup.characterRingInduction H (1 : R(H)) : R(G)) : G → ℂ) g =
      if QuotientGroup.mk' H g = 1 then (H.index : ℂ) else 0 := by
  classical
  letI : Fintype (G ⧸ H) := Fintype.ofFinite (G ⧸ H)
  -- Rewrite the induced trivial character as the regular quotient character, then use the
  -- textbook `if`-formula for the regular character.
  rw [induced_trivial_apply_eq_quotient_regular_value]
  by_cases hg : QuotientGroup.mk' H g = 1
  · rw [if_pos hg]
    simpa [Representation.leftRegular_character_eq_ite, hg, H.index_eq_card]
  · rw [if_neg hg]
    have hg_not_mem : g ∉ H := by
      intro hg_mem
      exact hg (by simpa using hg_mem)
    simpa [Representation.leftRegular_character_eq_ite, hg, hg_not_mem]

/-- Helper for Exercise 10-10.5-5: once the canonical quotient-group multiplication is known to be
commutative, the sum of all quotient linear characters has the same `if ... then [G : H] else 0`
formula as the regular quotient character. -/
theorem quotient_linearCharacter_sum_apply_eq_ite_index_zero_of_mul_comm
    (H : Subgroup G) [H.Normal]
    [DecidableEq (G ⧸ H)] (hcomm : ∀ a b : G ⧸ H, a * b = b * a)
    [Fintype ((G ⧸ H) →* ℂˣ)] (g : G) :
    (∑ χ : (G ⧸ H) →* ℂˣ, (χ (QuotientGroup.mk' H g) : ℂ)) =
      if QuotientGroup.mk' H g = 1 then (H.index : ℂ) else 0 := by
  classical
  letI : Fintype (G ⧸ H) := Fintype.ofFinite (G ⧸ H)
  letI : CommGroup (G ⧸ H) :=
    { QuotientGroup.Quotient.group H with
      mul_comm := hcomm }
  by_cases hg : QuotientGroup.mk' H g = 1
  · -- At the identity class, every linear character contributes `1`, and duality counts how many
    -- such characters there are.
    rw [if_pos hg]
    calc
      ∑ χ : (G ⧸ H) →* ℂˣ, (χ (QuotientGroup.mk' H g) : ℂ) =
          ∑ χ : (G ⧸ H) →* ℂˣ, (1 : ℂ) := by
            simp [hg]
      _ = (Fintype.card ((G ⧸ H) →* ℂˣ) : ℂ) := by
            simp
      _ = (Nat.card ((G ⧸ H) →* ℂˣ) : ℂ) := by
            simp [Nat.card_eq_fintype_card]
      _ = (Nat.card (G ⧸ H) : ℂ) := by
            congr 1
            exact
              CommGroup.card_monoidHom_of_hasEnoughRootsOfUnity (G := G ⧸ H) (M := ℂ)
      _ = (H.index : ℂ) := by
            simp [H.index_eq_card]
  · obtain ⟨φ, hφg⟩ :=
      CommGroup.exists_apply_ne_one_of_hasEnoughRootsOfUnity
        (G := G ⧸ H) (M := ℂ) hg
    let e : ((G ⧸ H) →* ℂˣ) ≃ ((G ⧸ H) →* ℂˣ) :=
      { toFun := fun χ ↦ φ * χ
        invFun := fun χ ↦ φ⁻¹ * χ
        left_inv := by
          intro χ
          simp
        right_inv := by
          intro χ
          simp }
    have hsum :
        ∑ χ : (G ⧸ H) →* ℂˣ, ((φ * χ) (QuotientGroup.mk' H g) : ℂ) =
          ∑ χ : (G ⧸ H) →* ℂˣ, (χ (QuotientGroup.mk' H g) : ℂ) := by
      -- Multiplication by the fixed character `φ` permutes the finite quotient dual.
      exact Fintype.sum_equiv e
        (fun χ : (G ⧸ H) →* ℂˣ ↦ ((φ * χ) (QuotientGroup.mk' H g) : ℂ))
        (fun χ : (G ⧸ H) →* ℂˣ ↦ (χ (QuotientGroup.mk' H g) : ℂ))
        (fun χ ↦ rfl)
    have hmul :
        ∑ χ : (G ⧸ H) →* ℂˣ, ((φ * χ) (QuotientGroup.mk' H g) : ℂ) =
          (φ (QuotientGroup.mk' H g) : ℂ) *
            ∑ χ : (G ⧸ H) →* ℂˣ, (χ (QuotientGroup.mk' H g) : ℂ) := by
      -- Pull the fixed scalar `φ(gH)` outside the translated sum.
      simp [Finset.mul_sum]
    have hfactor :
        (((φ (QuotientGroup.mk' H g) : ℂ) - 1) *
          ∑ χ : (G ⧸ H) →* ℂˣ, (χ (QuotientGroup.mk' H g) : ℂ)) = 0 := by
      -- Comparing the original sum with its translate forces the sum to vanish.
      calc
        (((φ (QuotientGroup.mk' H g) : ℂ) - 1) *
            ∑ χ : (G ⧸ H) →* ℂˣ, (χ (QuotientGroup.mk' H g) : ℂ)) =
            (φ (QuotientGroup.mk' H g) : ℂ) *
              ∑ χ : (G ⧸ H) →* ℂˣ, (χ (QuotientGroup.mk' H g) : ℂ) -
                ∑ χ : (G ⧸ H) →* ℂˣ, (χ (QuotientGroup.mk' H g) : ℂ) := by
                  ring
        _ = 0 := by
          rw [← hmul, hsum, sub_self]
    have hne : ((φ (QuotientGroup.mk' H g) : ℂ) - 1) ≠ 0 := by
      -- The chosen translating character avoids the value `1` exactly at the nontrivial class
      -- `gH`.
      intro hzero
      have hcast : (φ (QuotientGroup.mk' H g) : ℂ) = 1 := sub_eq_zero.mp hzero
      apply hφg
      ext
      simpa using hcast
    rw [if_neg hg]
    exact (mul_eq_zero.mp hfactor).resolve_left hne

/-- Helper for Exercise 10-10.5-5: the raw quotient class and the monoid-hom quotient class
coincide on the same element. -/
theorem quotient_mk_eq_mk' (H : Subgroup G) [H.Normal] (g : G) :
    (QuotientGroup.mk g : G ⧸ H) = QuotientGroup.mk' H g :=
  rfl

/-- Helper for Exercise 10-10.5-5: a group element lies in `H` exactly when its quotient class
from `QuotientGroup.mk'` is trivial. -/
theorem quotient_mk'_eq_one_iff (H : Subgroup G) [H.Normal] (g : G) :
    QuotientGroup.mk' H g = 1 ↔ g ∈ H := by
  rw [← quotient_mk_eq_mk' (H := H) g, QuotientGroup.eq_one_iff]


/-- Helper for Exercise 10-10.5-5: the quotient by a coatom is a simple group. -/
theorem isSimpleGroup_quotient_of_isCoatom
    (M : Subgroup G) [M.Normal] (hM : IsCoatom M) :
    IsSimpleGroup (G ⧸ M) := by
  -- The correspondence theorem identifies subgroups of `G ⧸ M` with subgroups of `G` containing
  -- `M`, and a coatom has only the two possibilities `M` and `⊤`.
  rw [isSimpleGroup_iff]
  constructor
  · obtain ⟨g, -, hg⟩ := SetLike.exists_of_lt (show M < ⊤ from hM.lt_top)
    refine ⟨QuotientGroup.mk' M g, 1, ?_⟩
    simpa using hg
  · intro N hN
    rcases (hM.le_iff.mp (QuotientGroup.le_comap_mk' M N)) with htop | hbot
    · right
      apply Subgroup.comap_injective (f := QuotientGroup.mk' M) (QuotientGroup.mk'_surjective M)
      simpa [htop]
    · left
      apply Subgroup.comap_injective (f := QuotientGroup.mk' M) (QuotientGroup.mk'_surjective M)
      simpa [hbot]

/-- Helper for Exercise 10-10.5-5: a coatom of an elementary finite group has prime-order
quotient. -/
theorem prime_card_quotient_of_isCoatom_of_isElementary
    (M : Subgroup G) (hM : IsCoatom M) (hG : IsElementary G) :
    (Nat.card (G ⧸ M)).Prime := by
  -- Maximal subgroups of a finite nilpotent group are normal, and the resulting simple nilpotent
  -- quotient is automatically commutative of prime order.
  letI : Group.IsNilpotent G := by
    rcases hG with ⟨p, hp⟩
    exact IsPElementary.isNilpotent hp
  letI : M.Normal :=
    Subgroup.NormalizerCondition.normal_of_coatom
      (G := G) (H := M) (normalizerCondition_of_isNilpotent (G := G)) hM
  letI : IsSimpleGroup (G ⧸ M) :=
    isSimpleGroup_quotient_of_isCoatom (G := G) M hM
  let hcomm : ∀ a b : G ⧸ M, a * b = b * a :=
    IsSimpleGroup.comm_iff_isSolvable.mpr inferInstance
  letI : CommGroup (G ⧸ M) :=
    { QuotientGroup.Quotient.group M with
      mul_comm := hcomm }
  simpa using
    (CommGroup.is_simple_iff_prime_card (α := G ⧸ M)).mp
      (inferInstance : IsSimpleGroup (G ⧸ M))

end Subgroup

/-- Helper for Exercise 10-10.5-5: once the canonical quotient-group multiplication is known to be
commutative, `Ind_H^G(1)` is the sum of the quotient linear characters pulled back along the
quotient map. -/
theorem induced_trivial_eq_sum_quotient_linearCharacters_of_mul_comm
    (H : Subgroup G) [H.Normal]
    (hcomm : ∀ a b : G ⧸ H, a * b = b * a)
    [Fintype ((G ⧸ H) →* ℂˣ)] :
    Subgroup.characterRingInduction H (1 : R(H)) =
      ∑ χ : (G ⧸ H) →* ℂˣ, (χ.comp (QuotientGroup.mk' H)).toCharacterRing := by
  classical
  ext g
  -- Normalize the left side to the quotient-regular `if` formula.
  rw [Subgroup.induced_trivial_apply_eq_ite_index_zero]
  -- Evaluate the finite sum termwise, then rewrite the quotient-character sum to the same scalar
  -- `if` expression.
  simpa [Finset.sum_apply] using
    (Subgroup.quotient_linearCharacter_sum_apply_eq_ite_index_zero_of_mul_comm
      (H := H) hcomm g).symm


/-- Helper for Exercise 10-10.5-5: restricting a complex-valued class function to a subgroup is a
`ℤ`-algebra map. -/
private def functionRestriction (H : Subgroup G) : (G → ℂ) →ₐ[ℤ] (H → ℂ) where
  toFun χ := fun h ↦ χ h
  map_zero' := rfl
  map_one' := rfl
  map_add' χ ψ := by
    ext h
    rfl
  map_mul' χ ψ := by
    ext h
    rfl
  commutes' n := by
    ext h
    rfl

/-- Helper for Exercise 10-10.5-5: restricting a virtual character to a subgroup stays inside the
subgroup character ring. -/
theorem restrict_mem_characterRing_local
    (H : Subgroup G) (χ : R(G)) :
    (fun h : H ↦ (χ : G → ℂ) h) ∈ R(H) := by
  -- Restriction is an algebra map, so it suffices to check it on the irreducible generators of
  -- the ambient character ring.
  change functionRestriction H χ ∈ R(H)
  have hmap_le : R(G).map (functionRestriction H) ≤ R(H) := by
    refine (Subalgebra.gc_map_comap (functionRestriction H)).l_le ?_
    rw [Representation.characterRingOverField]
    refine (Algebra.adjoin_le_iff).2 ?_
    intro ψ hψ
    rcases hψ with ⟨ρ, hfd, hirr, rfl⟩
    letI : FiniteDimensional ℂ ρ := hfd
    -- Restriction of a finite-dimensional representation restricts its character pointwise.
    change functionRestriction H (ρ.ρ.character) ∈ R(H)
    simpa [functionRestriction] using
      (Representation.rep_character_mem_characterRingOverField (K := ℂ)
        (ρ := Rep.res H.subtype ρ))
  exact hmap_le ⟨χ, χ.property, rfl⟩

namespace Subgroup

/-- Helper for Exercise 10-10.5-5: multiplying an induced class function by an ambient virtual
character can be pushed inside induction after restriction. -/
theorem induced_mul_eq_induced_mul_restriction_local
    (H : Subgroup G) (ψ : H → ℂ) (χ : R(G)) :
    Ind[H](ψ) * (χ : G → ℂ) = Ind[H](fun h : H ↦ ψ h * χ h) := by
  classical
  -- Compare the induction formulas pointwise and use that every virtual character is a class
  -- function.
  ext x
  simp only [Pi.mul_apply, Subgroup.inducedClassFunction]
  rw [mul_assoc, Finset.sum_mul]
  congr 1
  refine Finset.sum_congr rfl ?_
  intro s hs_univ
  by_cases hs : s⁻¹ * x * s ∈ H
  · have hs' : s⁻¹ * (x * s) ∈ H := by
      simpa [mul_assoc] using hs
    have hχ :
        (χ : G → ℂ) (s⁻¹ * x * s) = (χ : G → ℂ) x := by
      exact (Representation.isClassFunction_of_mem_characterRingOverField (K := ℂ)
        (χ : G → ℂ) χ.property).eq_of_isConj <| isConj_iff.2 ⟨s, by group⟩
    have hχ' : (χ : G → ℂ) (s⁻¹ * (x * s)) = (χ : G → ℂ) x := by
      simpa [mul_assoc] using hχ
    simp [hs', hχ', mul_comm, mul_assoc]
  · simp [hs]


end Subgroup

end

end Representation
