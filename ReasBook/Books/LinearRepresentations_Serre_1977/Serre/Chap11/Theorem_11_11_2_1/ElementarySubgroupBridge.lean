import LinearRepresentations_Serre_1977.Serre.Chap11.Theorem_11_11_2_1.TensorCharacterBridge

noncomputable section

universe u v w

namespace Representation

section FrobeniusTheorem

open scoped Representation TensorProduct BigOperators SubgroupInduction

variable {G : Type u} [Group G]
variable {A : Type v} [CommRing A] [Algebra A ℂ]

/-- Helper for Theorem 11-11.2-1: a finite group has finitely many conjugacy classes. -/
local instance elementarySubgroupBridge_conjClasses_fintype
    (H : Type w) [Group H] [Finite H] : Fintype (ConjClasses H) :=
  Fintype.ofFinite (ConjClasses H)

/-- Helper for Theorem 11-11.2-1: finite subgroups inherit their canonical `Fintype` structure. -/
local instance elementarySubgroupBridge_subgroup_fintype [Finite G] (H : Subgroup G) : Fintype H :=
  Fintype.ofFinite H

/-- Helper for Theorem 11-11.2-1: every finite cyclic group is elementary. -/
theorem isElementary_of_isCyclic_local
    {H : Type w} [Group H] [Finite H] (hH : IsCyclic H) :
    IsElementary H := by
  -- Choose a prime larger than `|H|`; then `H = H × ⊥` is a `p`-elementary decomposition.
  obtain ⟨p, hpge, hpprime⟩ := Nat.exists_infinite_primes (Nat.card H + 1)
  refine ⟨p, ⊤, ⊥, ?_⟩
  refine ⟨hpprime, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- The trivial `p`-group factor is finite.
    infer_instance
  · -- The cyclic factor is the whole group.
    exact (Subgroup.topEquiv : (⊤ : Subgroup H) ≃* H).isCyclic.2 hH
  · -- The chosen prime does not divide the cyclic factor order.
    have hlt : Nat.card H < p := lt_of_lt_of_le (Nat.lt_succ_self _) hpge
    have hcard_top : Nat.card (⊤ : Subgroup H) = Nat.card H :=
      Nat.card_congr Subgroup.topEquiv.toEquiv
    rw [Nat.Prime.coprime_iff_not_dvd hpprime]
    rw [hcard_top]
    exact Nat.not_dvd_of_pos_of_lt Nat.card_pos hlt
  · -- The trivial subgroup is a `p`-group.
    simpa using (IsPGroup.of_bot (p := p) : IsPGroup p (⊥ : Subgroup H))
  · -- Centralizing the trivial subgroup is automatic.
    intro c hc y hy
    have hy1 : y = 1 := by simpa using hy
    simpa [hy1]
  · -- `⊤` and `⊥` are complementary.
    simpa using Subgroup.isComplement'_top_bot (G := H)

/-- Helper for Theorem 11-11.2-1: elementary groups stay elementary under multiplication
equivalences. -/
theorem isElementary_of_mulEquiv_local
    {H : Type w} [Group H] {J : Type v} [Group J]
    (e : H ≃* J) (hH : IsElementary H) :
    IsElementary J := by
  rcases hH with ⟨p, C, P, hCP⟩
  -- Transport the textbook `p`-elementary decomposition across the chosen equivalence.
  letI : Finite H := (show IsPElementary p H from ⟨C, P, hCP⟩).finite
  letI : Finite P := hCP.finite_pGroup_factor
  letI : Finite J := Finite.of_equiv H e.toEquiv
  letI : IsCyclic C := hCP.cyclic
  refine ⟨p, C.map e.toMonoidHom, P.map e.toMonoidHom, ?_⟩
  refine ⟨hCP.prime, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact Finite.of_equiv P (Subgroup.equivMapOfInjective P e.toMonoidHom e.injective)
  · let eC : C ≃* C.map e.toMonoidHom :=
      Subgroup.equivMapOfInjective C e.toMonoidHom e.injective
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

/-- Helper for Theorem 11-11.2-1: subgroups of elementary groups are elementary. -/
theorem subgroup_isElementary_of_isElementary_local
    {H : Type w} [Group H] (K : Subgroup H) (hH : IsElementary H) :
    IsElementary K := by
  rcases hH with ⟨p, hpH⟩
  rcases hpH with ⟨C, P, hCP⟩
  letI : Fact (Nat.Prime p) := ⟨hCP.prime⟩
  letI : Finite H := (show IsPElementary p H from ⟨C, P, hCP⟩).finite
  letI : Finite K := Finite.of_injective ((↑) : K → H) Subtype.val_injective
  let C' : Subgroup K := (K ⊓ C).subgroupOf K
  let P' : Subgroup K := (K ⊓ P).subgroupOf K
  letI : Finite ↥C' := Finite.of_injective ((↑) : C' → K) Subtype.val_injective
  letI : Finite ↥P' := Finite.of_injective ((↑) : P' → K) Subtype.val_injective
  have hC'card : Nat.card ↥C' = Nat.card ↥(K ⊓ C) := by
    exact Nat.card_congr
      (Subgroup.subgroupOfEquivOfLe (show K ⊓ C ≤ K from inf_le_left)).toEquiv
  -- Restrict the ambient elementary decomposition to the chosen subgroup.
  refine ⟨p, C', P', ?_⟩
  refine ⟨hCP.prime, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · infer_instance
  · letI : IsCyclic ↥C := hCP.cyclic
    letI : IsCyclic ↥(K ⊓ C) :=
      Subgroup.isCyclic_of_le (show K ⊓ C ≤ C from inf_le_right)
    exact
      isCyclic_of_surjective
        (Subgroup.subgroupOfEquivOfLe (show K ⊓ C ≤ K from inf_le_left)).symm.toMonoidHom
        (Subgroup.subgroupOfEquivOfLe (show K ⊓ C ≤ K from inf_le_left)).symm.surjective
  · have hdiv : Nat.card ↥(K ⊓ C) ∣ Nat.card ↥C := by
      exact Subgroup.card_dvd_of_le (show K ⊓ C ≤ C from inf_le_right)
    rw [hC'card]
    exact hCP.coprime_card.of_dvd_right hdiv
  · have hPsub : IsPGroup p ↥((K ⊓ P).subgroupOf P) := by
      exact hCP.isPGroup.to_subgroup ((K ⊓ P).subgroupOf P)
    have hPinf_right : IsPGroup p ↥(K ⊓ P) := by
      exact hPsub.of_equiv
        (Subgroup.subgroupOfEquivOfLe (show K ⊓ P ≤ P from inf_le_right))
    exact hPinf_right.of_equiv
      (Subgroup.subgroupOfEquivOfLe (show K ⊓ P ≤ K from inf_le_left)).symm
  · intro c hc u hu
    have hcC : ((c : K) : H) ∈ C := by
      exact (show ((c : K) : H) ∈ K ⊓ C from hc).2
    have huP : ((u : K) : H) ∈ P := by
      exact (show ((u : K) : H) ∈ K ⊓ P from hu).2
    apply Subtype.ext
    simpa using hCP.centralizes hcC ((u : K) : H) huP
  · refine Subgroup.isComplement'_of_disjoint_and_mul_eq_univ ?_ ?_
    · rw [Subgroup.disjoint_def]
      intro x hxC hxP
      have hxCG : ((x : K) : H) ∈ C := by
        exact (show ((x : K) : H) ∈ K ⊓ C from hxC).2
      have hxPG : ((x : K) : H) ∈ P := by
        exact (show ((x : K) : H) ∈ K ⊓ P from hxP).2
      have hxbot : ((x : K) : H) ∈ (⊥ : Subgroup H) := by
        have hbot : C ⊓ P = (⊥ : Subgroup H) := disjoint_iff.mp hCP.isComplement.disjoint
        exact hbot ▸ ⟨hxCG, hxPG⟩
      apply Subtype.ext
      simpa using hxbot
    · apply Set.eq_univ_iff_forall.2
      intro x
      let xr : K := pRegularComponent p x
      let xu : K := pUnipotentComponent p x
      have hdecomp :
          IsPComponentDecomposition p x xu xr := by
        simpa [xu, xr] using
          p_component_decomposition_exists (p := p) x (isOfFinOrder_of_finite x)
      have hxrC : (xr : H) ∈ C := by
        have hxrReg : IsPRegular p (xr : H) := by
          simpa [IsPRegular, Subgroup.orderOf_mk, xr] using hdecomp.isPRegular
        change (xr : H) ∈ (C : Set H)
        rw [hCP.cyclic_factor_eq_setOf_isPRegular]
        exact hxrReg
      have hxuP : (xu : H) ∈ P := by
        have hxuElt : IsPElement p (xu : H) := by
          simpa [IsPElement, Subgroup.orderOf_mk, xu] using hdecomp.isPElement
        change (xu : H) ∈ (P : Set H)
        rw [hCP.p_group_factor_eq_setOf_isPElement]
        exact hxuElt
      have hxr_mem : xr ∈ C' := by
        change (xr : H) ∈ K ⊓ C
        exact ⟨xr.2, hxrC⟩
      have hxu_mem : xu ∈ P' := by
        change (xu : H) ∈ K ⊓ P
        exact ⟨xu.2, hxuP⟩
      refine ⟨xr, hxr_mem, xu, hxu_mem, ?_⟩
      calc
        xr * xu = xu * xr := by
          simpa using hdecomp.commute.symm
        _ = x := hdecomp.mul_eq

/-- Helper for Theorem 11-11.2-1: evaluating a basis expansion of bundled class functions
recovers the original pointwise value. -/
theorem classFunction_basis_expansion_apply_local
    {H : Type*} [Group H] [Finite H]
    {ι : Type*} [Fintype ι]
    (b : Module.Basis ι ℂ (classFunctionSubmodule ℂ H))
    (x : classFunctionSubmodule ℂ H) (h : H) :
    (∑ j, ((b.repr x j) • b j : classFunctionSubmodule ℂ H)) h = x h := by
  -- This is the standard basis expansion `b.sum_repr x = x`, evaluated at the chosen element.
  exact congrArg (fun z : classFunctionSubmodule ℂ H ↦ z h) (b.sum_repr x)

/-- Helper for Theorem 11-11.2-1: in the irreducible-character basis attached to a complete
family, each coordinate is the normalized pairing with the matching irreducible character. -/
theorem repr_irreducible_character_basis_eq_pairing_local
    {H : Type}
    [Group H] [Finite H]
    {ι : Type*}
    (π : ι → FDRep ℂ H)
    (hπ_pairwise : CategoryTheory.PairwiseNonisomorphic π)
    (hπ_complete : IsCompleteIrreducibleFamily π)
    [Fintype ι]
    (x : classFunctionSubmodule ℂ H) (i : ι) :
    (Representation.irreducibleCharacters_basis_of_classFunctionSubspace_of_complete_family
        π hπ_pairwise hπ_complete).repr x i =
      Representation.groupFunctionPairingOverField ℂ (x : H → ℂ) (π i).character := by
  classical
  let _ : Fintype H := Fintype.ofFinite H
  let _ : NeZero (Nat.card H : ℂ) := ⟨by
    exact_mod_cast Nat.card_pos.ne'⟩
  let b := Representation.irreducibleCharacters_basis_of_classFunctionSubspace_of_complete_family
    π hπ_pairwise hπ_complete
  let coordLinear : classFunctionSubmodule ℂ H →ₗ[ℂ] ℂ :=
    { toFun := fun y ↦ b.repr y i
      map_add' := by
        intro y z
        simp
      map_smul' := by
        intro a y
        simp }
  let pairLinear : classFunctionSubmodule ℂ H →ₗ[ℂ] ℂ :=
    { toFun := fun y ↦
        Representation.groupFunctionPairingOverField ℂ (y : H → ℂ) (π i).character
      map_add' := by
        intro y z
        simpa using Representation.groupFunctionPairing_add_left
          (y : H → ℂ) (z : H → ℂ) (π i).character
      map_smul' := by
        intro a y
        simpa using Representation.groupFunctionPairing_smul_left
          a (y : H → ℂ) (π i).character }
  have hmaps : coordLinear = pairLinear := by
    -- Compare the two linear functionals on the irreducible-character basis itself.
    apply b.ext
    intro j
    have hcoord_j : coordLinear (b j) = if i = j then 1 else 0 := by
      simpa [eq_comm] using
        (show coordLinear (b j) = if j = i then 1 else 0 by
          simp [coordLinear, Module.Basis.repr_self, Finsupp.single_apply])
    have hpair_j : pairLinear (b j) = if i = j then 1 else 0 := by
      by_cases hij : i = j
      · subst j
        letI : CategoryTheory.Simple (π i) := hπ_complete.isSimple i
        have hself_iso : Nonempty (π i ≅ π i) := ⟨CategoryTheory.Iso.refl _⟩
        calc
          pairLinear (b i) =
              Representation.groupFunctionPairingOverField ℂ
                (π i).character (π i).character := by
            simp [pairLinear, b,
              Representation.irreducibleCharacters_basis_of_classFunctionSubspace_of_complete_family_apply]
          _ = 1 := by
            simpa [Representation.groupFunctionPairing_eq_card_inv_sum_apply_mul_inv_apply,
              hself_iso] using
              (FDRep.char_orthonormal (π i) (π i))
          _ = if i = i then 1 else 0 := by
            simp
      · have hji : j ≠ i := fun h ↦ hij h.symm
        letI : CategoryTheory.Simple (π j) := hπ_complete.isSimple j
        letI : CategoryTheory.Simple (π i) := hπ_complete.isSimple i
        have hnot : ¬ Nonempty (π j ≅ π i) := hπ_pairwise hji
        calc
          pairLinear (b j) =
              Representation.groupFunctionPairingOverField ℂ
                (π j).character (π i).character := by
            simp [pairLinear, b,
              Representation.irreducibleCharacters_basis_of_classFunctionSubspace_of_complete_family_apply]
          _ = 0 := by
            simpa [Representation.groupFunctionPairing_eq_card_inv_sum_apply_mul_inv_apply,
              hnot] using
              (FDRep.char_orthonormal (π j) (π i))
          _ = if i = j then 1 else 0 := by
            simp [hij]
    exact hcoord_j.trans hpair_j.symm
  -- Apply the functional identity to the chosen bundled class function.
  have hmaps_apply := congrArg
    (fun f : classFunctionSubmodule ℂ H →ₗ[ℂ] ℂ ↦ f x) hmaps
  simpa [coordLinear, pairLinear] using hmaps_apply

/-- Helper for Theorem 11-11.2-1: a degree-`1` character on `K ≤ H` transports to the image
subgroup `K.map H.subtype`. -/
def mappedLinearCharacter_local
    (H : Subgroup G) (K : Subgroup H) (χ : K →* ℂˣ) :
    K.map H.subtype →* ℂˣ :=
  χ.comp (K.equivMapOfInjective H.subtype H.subtype_injective).symm.toMonoidHom

/-- Helper for Theorem 11-11.2-1: restricting the mapped subgroup `K.map H.subtype` back to `H`
recovers the original subgroup `K`. -/
theorem subgroup_chain_inner_subgroup_eq_local
    (H : Subgroup G) (K : Subgroup H) :
    ((K.map H.subtype).subgroupOf H : Subgroup H) = K := by
  -- The image subgroup consists exactly of those elements of `H` coming from `K`.
  ext k
  change k.1 ∈ K.map H.subtype ↔ k ∈ K
  constructor
  · intro hk
    rcases hk with ⟨x, hx, hxk⟩
    have hxeq : x = k := by
      apply Subtype.ext
      simpa using hxk
    simpa [hxeq] using hx
  · intro hk
    exact ⟨k, hk, rfl⟩

/-- Helper for Theorem 11-11.2-1: the mapped subgroup `K.map H.subtype` is contained in `H`. -/
theorem subgroup_chain_map_le_local
    (H : Subgroup G) (K : Subgroup H) :
    K.map H.subtype ≤ H := by
  -- Every element of the mapped subgroup is literally the image of an element of `K ≤ H`.
  intro x hx
  rcases hx with ⟨y, -, rfl⟩
  exact y.property

/-- Helper for Theorem 11-11.2-1: reindexing along `K ≃ K.map H.subtype` identifies the ambient
pairing with the nested restriction pairing. -/
theorem mapped_linear_character_pairing_eq_nested_restriction_local
    [Finite G]
    (φ : classFunctionSubmodule ℂ G)
    (H : Subgroup G) (K : Subgroup H) (χ : K →* ℂˣ) :
    ⟪(mappedLinearCharacter_local (G := G) H K χ).toCharacterRing,
        Subgroup.classFunctionRestriction (K.map H.subtype) φ⟫ =
      ⟪χ.toCharacterRing,
        Subgroup.classFunctionRestriction K (Subgroup.classFunctionRestriction H φ)⟫ := by
  classical
  let e : K ≃* K.map H.subtype := K.equivMapOfInjective H.subtype H.subtype_injective
  let nested : K → ℂ := fun y ↦
    (χ.toCharacterRing : K → ℂ) y *
      ((Subgroup.classFunctionRestriction K (Subgroup.classFunctionRestriction H φ) :
          classFunctionSubmodule ℂ K) : K → ℂ) y⁻¹
  let ambient : K.map H.subtype → ℂ := fun y ↦
    (((mappedLinearCharacter_local (G := G) H K χ).toCharacterRing :
        K.map H.subtype → ℂ) y) *
      ((Subgroup.classFunctionRestriction (K.map H.subtype) φ :
          classFunctionSubmodule ℂ (K.map H.subtype)) : K.map H.subtype → ℂ) y⁻¹
  -- Rewrite both pairings as normalized sums and reindex along the subgroup equivalence.
  rw [Representation.groupFunctionPairing_eq_card_inv_sum_apply_mul_inv_apply,
    Representation.groupFunctionPairing_eq_card_inv_sum_apply_mul_inv_apply]
  have hcardNat : Nat.card (K.map H.subtype) = Nat.card K :=
    (Nat.card_congr e.toEquiv).symm
  have hcard : ((Nat.card (K.map H.subtype) : ℕ) : ℂ) = (Nat.card K : ℂ) := by
    exact_mod_cast hcardNat
  rw [hcard]
  refine congrArg (fun z : ℂ ↦ (Nat.card K : ℂ)⁻¹ * z) ?_
  change (∑ t : K.map H.subtype, ambient t) = ∑ t : K, nested t
  exact (Fintype.sum_equiv e nested ambient (by
    intro y
    -- After transporting along `e`, both the mapped linear character and the nested restriction
    -- reduce to the original subgroup data.
    dsimp [nested, ambient]
    congr 1
    simp [e, mappedLinearCharacter_local])).symm

/-- Helper for Theorem 11-11.2-1: pairing information on every elementary subgroup descends from
`K.map H.subtype` back to the nested subgroup `K ≤ H`. -/
theorem pairing_mem_range_on_nested_elementary_linear_character_local
    [Finite G]
    (φ : classFunctionSubmodule ℂ G)
    (hpair : ∀ (H : Subgroup G) (_ : IsElementary H) (χ : H →* ℂˣ),
      ⟪χ.toCharacterRing, Subgroup.classFunctionRestriction H φ⟫ ∈ Set.range (algebraMap A ℂ))
    (H : Subgroup G) (hH : IsElementary H) (K : Subgroup H) (χ : K →* ℂˣ) :
    ⟪χ.toCharacterRing,
        Subgroup.classFunctionRestriction K (Subgroup.classFunctionRestriction H φ)⟫ ∈
      Set.range (algebraMap A ℂ) := by
  have hK : IsElementary K := subgroup_isElementary_of_isElementary_local K hH
  have hKmap : IsElementary (K.map H.subtype) :=
    isElementary_of_mulEquiv_local
      (K.equivMapOfInjective H.subtype H.subtype_injective) hK
  have hmap :=
    hpair (K.map H.subtype) hKmap (mappedLinearCharacter_local (G := G) H K χ)
  -- Reindex the ambient pairing on `K.map H.subtype` back to the original subgroup `K`.
  rw [← mapped_linear_character_pairing_eq_nested_restriction_local
    (G := G) (φ := φ) H K χ]
  exact hmap

end FrobeniusTheorem

end Representation
