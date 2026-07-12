import LinearRepresentations_Serre_1977.Chap16.Exercise_16_16_1_11.Common

noncomputable section

open CategoryTheory
open Representation
open scoped Representation SubgroupInduction

namespace Exercise_16_16_1_11

section

variable {G : Type} [Group G]

local notation "DivisorIndex" => { d : ℕ // d ∣ Nat.card G }

variable {A : Type} [CommRing A] [IsLocalRing A] [Algebra A ℚ] [IsFractionRing A ℚ]

variable [CharP (IsLocalRing.ResidueField A) 5]
variable [Finite G] [IsCyclic G] (hG : Nat.card G = 4)

local instance rationalInfrastructureFintype : Fintype G := Fintype.ofFinite G
local instance rationalInfrastructureCommGroup : CommGroup G := IsCyclic.commGroup
local instance rationalInfrastructureIsDomain : IsDomain A := (IsFractionRing.injective A ℚ).isDomain
attribute [local instance] Classical.decEq Classical.propDecidable

/-- Helper for Exercise 16-16.1-11: the divisor-index type for a finite group is finite. -/
noncomputable def divisorIndexFintype : Fintype DivisorIndex := by
  classical
  let s : Set ℕ := {n | n ∣ Nat.card G}
  have hs : s.Finite := by
    refine (Set.finite_le_nat (Nat.card G)).subset ?_
    intro n hn
    exact Nat.le_of_dvd Nat.card_pos hn
  exact hs.fintype

local instance rationalInfrastructureDivisorIndexFintype : Fintype DivisorIndex :=
  divisorIndexFintype (G := G)

local notation "d₁" => cyclicOrderFourDivisorIndexOne hG
local notation "d₂" => cyclicOrderFourDivisorIndexTwo hG
local notation "d₄" => cyclicOrderFourDivisorIndexFour hG

/-- Helper for Exercise 16-16.1-11: the canonical subgroup `G_d` in the rational-character
section. This duplicates the source-facing Chapter 16 API that is absent from the current repo
snapshot. -/
noncomputable def cyclicSubgroupOfIndex
    (d' : DivisorIndex) : Subgroup G :=
  (powMonoidHom d'.1 : G →* G).range

local prefix:max "G_ " => cyclicSubgroupOfIndex

/-- Helper for Exercise 16-16.1-11: in the rational-character section, the canonical subgroup
`G_d` has index `d`. -/
theorem cyclicSubgroupOfIndex_index
    (d' : DivisorIndex) :
    (G_ d').index = d'.1 := by
  have hdvd : d'.1 ∣ Fintype.card G := by
    simpa [Nat.card_eq_fintype_card] using d'.2
  simpa [cyclicSubgroupOfIndex, Nat.gcd_eq_right hdvd] using
    (IsCyclic.index_powMonoidHom_range (G := G) d'.1)

/-- Helper for Exercise 16-16.1-11: Serre's permutation character `ψ_d` is the induction of the
trivial character from the canonical subgroup `G_d`. -/
noncomputable def cyclicSubgroupIndexInducedTrivialRationalCharacter
    (d' : DivisorIndex) : R[ℚ](G) :=
  Subgroup.characterRingOverFieldInduction (G_ d') ℚ 1

local prefix:max "ψ_ " => cyclicSubgroupIndexInducedTrivialRationalCharacter

/-- Helper for Exercise 16-16.1-11: a positive divisor of `2` is either `1` or `2`. -/
theorem divisor_of_two_eq_one_or_two
    {n : ℕ} (hn : n ∈ Nat.divisors 2) :
    n = 1 ∨ n = 2 := by
  rw [Nat.mem_divisors] at hn
  have hnle : n ≤ 2 := Nat.le_of_dvd (by decide) hn.1
  interval_cases n <;> simp at hn
  · simp
  · simp

/-- Helper for Exercise 16-16.1-11: a positive divisor of `4` is `1`, `2`, or `4`. -/
theorem divisor_of_four_eq_one_or_two_or_four
    {n : ℕ} (hn : n ∈ Nat.divisors 4) :
    n = 1 ∨ n = 2 ∨ n = 4 := by
  rw [Nat.mem_divisors] at hn
  have hnle : n ≤ 4 := Nat.le_of_dvd (by decide) hn.1
  interval_cases n <;> simp at hn
  · simp
  · simp
  · simp

/-- Helper for Exercise 16-16.1-11: every divisor index of a cyclic group of order `4` is one of
`1`, `2`, or `4`. -/
theorem divisorIndex_eq_one_or_two_or_four
    (hcardG : Nat.card G = 4)
    (d' : DivisorIndex) :
    d'.1 = 1 ∨ d'.1 = 2 ∨ d'.1 = 4 := by
  have hdmem : d'.1 ∈ Nat.divisors 4 := by
    have hcard : Fintype.card G = 4 := by
      simpa using hcardG
    rw [Nat.mem_divisors]
    exact ⟨by simpa [Nat.card_eq_fintype_card, hcard] using d'.2, by decide⟩
  exact divisor_of_four_eq_one_or_two_or_four hdmem

/-- Helper for Exercise 16-16.1-11: in a cyclic group of order `4`, the subgroup `G_4` is
trivial. -/
theorem mem_cyclicSubgroupOfIndexFour_iff_eq_one
    (g : G) :
    g ∈ G_ d₄ ↔ g = 1 := by
  constructor
  · rintro ⟨x, rfl⟩
    have hcard : Fintype.card G = 4 := by
      simpa using hG
    simpa [Nat.card_eq_fintype_card, hcard] using (pow_card_eq_one (x := x))
  · intro hg
    subst hg
    simpa [cyclicSubgroupOfIndex] using
      (show ∃ x : G, x ^ 4 = (1 : G) by exact ⟨1, by simp⟩)

/-- Helper for Exercise 16-16.1-11: because the group is abelian, the subgroup permutation
character `ℓ_H^G` takes the value `H.index` on `H` and `0` outside `H`. -/
theorem rational_subgroup_permutation_character_apply
    (H : Subgroup G) (g : G) :
    (((Subgroup.characterRingOverFieldInduction H ℚ 1 : R[ℚ](G)) : G → ℚ) g) =
      if g ∈ H then H.index else 0 := by
  classical
  -- `IsClassFunction` is ambiguous here (both `_root_.IsClassFunction` and
  -- `Representation.IsClassFunction` are in scope); the transversal lemma needs the `_root_` one.
  have hψ : _root_.IsClassFunction (1 : H → ℚ) := by
    refine ⟨?_⟩
    intro a b _hab
    rfl
  obtain ⟨S, hS, h1S⟩ := H.exists_isComplement_left (1 : G)
  let R : Finset G := (Set.toFinite S).toFinset
  have hR : Subgroup.IsComplement (R : Set G) (H : Set G) := by
    simpa [R] using hS
  have hcardR : R.card = H.index := by
    simpa [R] using hR.card_left
  haveI : NeZero (Nat.card H : ℚ) :=
    ⟨Nat.cast_ne_zero.mpr (Nat.card_ne_zero.mpr ⟨⟨1, H.one_mem⟩, inferInstance⟩)⟩
  rw [Subgroup.characterRingOverFieldInduction_apply]
  change Subgroup.inducedClassFunction H (1 : H → ℚ) g = _
  rw [Subgroup.induced_class_function_eq_sum_over_left_transversal
    (H := H) (ψ := (1 : H → ℚ)) hψ (R := R) (hR := hR) (x := g)]
  have hconj (r : G) : r⁻¹ * g * r = g := by
    simp [mul_assoc]
  have hterm (r : G) :
      (if hr : r⁻¹ * g * r ∈ H then (1 : H → ℚ) ⟨r⁻¹ * g * r, hr⟩ else 0) =
        if g ∈ H then 1 else 0 := by
    by_cases hgH : g ∈ H
    · have hr : r⁻¹ * g * r ∈ H := by
        simpa [hconj r] using hgH
      simp [hr, hgH]
    · have hr : ¬ r⁻¹ * g * r ∈ H := by
        simpa [hconj r] using hgH
      simp [hr, hgH]
  rw [show
      (∑ r ∈ R, if hr : r⁻¹ * g * r ∈ H then (1 : H → ℚ) ⟨r⁻¹ * g * r, hr⟩ else 0) =
        ∑ r ∈ R, (if g ∈ H then 1 else 0) by
      refine Finset.sum_congr rfl ?_
      intro r hr
      exact hterm r]
  by_cases hgH : g ∈ H
  · simp [hgH, hcardR]
  · simp [hgH]

/-- Helper for Exercise 16-16.1-11: the rational permutation character `ψ₂` takes the values
`2` on `G_2` and `0` off `G_2`. -/
theorem rational_index_two_permutation_character_apply
    (g : G) :
    (ψ_ d₂ : G → ℚ) g = if g ∈ G_ d₂ then 2 else 0 := by
  have hindex : (G_ d₂).index = 2 := by
    simpa using cyclicSubgroupOfIndex_index (G := G) d₂
  rw [cyclicSubgroupIndexInducedTrivialRationalCharacter]
  rw [rational_subgroup_permutation_character_apply (G := G) (H := G_ d₂) g]
  simp [hindex]

/-- Helper for Exercise 16-16.1-11: the rational permutation character `ψ₄` is the regular
character of `G`. -/
theorem rational_index_four_permutation_character_apply
    (g : G) :
    (ψ_ d₄ : G → ℚ) g = if g = 1 then 4 else 0 := by
  have hindex : (G_ d₄).index = 4 := by
    simpa using cyclicSubgroupOfIndex_index (G := G) d₄
  rw [cyclicSubgroupIndexInducedTrivialRationalCharacter]
  rw [rational_subgroup_permutation_character_apply (G := G) (H := G_ d₄) g]
  simp [hindex, mem_cyclicSubgroupOfIndexFour_iff_eq_one (G := G) (hG := hG) g]

/-- Helper for Exercise 16-16.1-11: over any field, the character of a permutation
representation counts fixed points. -/
theorem fdRep_ofMulAction_character_eq_ncard_fixedBy_field
    {K : Type} [Field K]
    (X : Type) [MulAction G X] [Finite X] (g : G) :
    (FDRep.of (ofMulAction K G X)).character g = ↑(MulAction.fixedBy X g).ncard := by
  classical
  letI : Fintype X := Fintype.ofFinite X
  change (ofMulAction K G X).character g = ↑(MulAction.fixedBy X g).ncard
  calc
    (ofMulAction K G X).character g
      = Matrix.trace
          (LinearMap.toMatrix Finsupp.basisSingleOne Finsupp.basisSingleOne
            ((ofMulAction K G X) g)) := by
            rw [Representation.character,
              LinearMap.trace_eq_matrix_trace K Finsupp.basisSingleOne]
    _ = ∑ x : X, if g • x = x then 1 else 0 := by
          simp [Matrix.trace, LinearMap.toMatrix_apply, Representation.ofMulAction_single,
            Finsupp.single_apply]
    _ = ↑((Finset.univ.filter fun x : X ↦ g • x = x).card) := by
          simp
    _ = ↑((MulAction.fixedBy X g).toFinset.card) := by
          congr
          ext x
          simp [MulAction.mem_fixedBy]
    _ = ↑(MulAction.fixedBy X g).ncard := by
          rw [← Set.ncard_eq_toFinset_card']

/-- Helper for Exercise 16-16.1-11: on the quotient by the unique index-`2` subgroup, fixing one
coset is equivalent to belonging to that subgroup. -/
theorem quotient_index_two_fixed_iff_mem_general
    (g : G) (x : G ⧸ G_ d₂) :
    x ∈ MulAction.fixedBy (G ⧸ G_ d₂) g ↔ g ∈ G_ d₂ := by
  rcases Quotient.exists_rep x with ⟨a, rfl⟩
  rw [MulAction.mem_fixedBy]
  change QuotientGroup.mk (g * a) = QuotientGroup.mk a ↔ g ∈ G_ d₂
  rw [QuotientGroup.eq_iff_div_mem]
  simp [div_eq_mul_inv, mul_assoc]

/-- Helper for Exercise 16-16.1-11: the quotient by the unique index-`2` subgroup has
cardinality `2`. -/
theorem quotient_index_two_card_general :
    Nat.card (G ⧸ G_ d₂) = 2 := by
  simpa [Subgroup.index_eq_card] using cyclicSubgroupOfIndex_index (G := G) d₂

/-- Helper for Exercise 16-16.1-11: the rational class of the quotient permutation representation
has character `ψ₂`. -/
theorem rational_quotient_permutation_class_character :
    finiteRepGrothendieckCharacter ℚ G
        [FDRep.of (ofMulAction ℚ G (G ⧸ G_ d₂))]₀ =
      ψ_ d₂ := by
  ext g
  rw [finiteRepGrothendieckCharacter_class]
  rw [fdRep_ofMulAction_character_eq_ncard_fixedBy_field
    (G := G) (K := ℚ) (X := G ⧸ G_ d₂)]
  rw [rational_index_two_permutation_character_apply (G := G) (hG := hG)]
  by_cases hg : g ∈ G_ d₂
  · have hfixed : MulAction.fixedBy (G ⧸ G_ d₂) g = Set.univ := by
      ext x
      constructor
      · intro _
        simp
      · intro _
        exact (quotient_index_two_fixed_iff_mem_general (G := G) (hG := hG) (g := g)
          (x := x)).2 hg
    rw [hfixed, if_pos hg]
    have hcardQ : Fintype.card (G ⧸ G_ d₂) = 2 := by
      simpa [Nat.card_eq_fintype_card] using
        quotient_index_two_card_general (G := G) (hG := hG)
    norm_num [hcardQ]
  · have hfixed : MulAction.fixedBy (G ⧸ G_ d₂) g = (∅ : Set (G ⧸ G_ d₂)) := by
      ext x
      constructor
      · intro hx
        exact False.elim <|
          hg ((quotient_index_two_fixed_iff_mem_general (G := G) (hG := hG) (g := g)
            (x := x)).1 hx)
      · intro hx
        simp at hx
    rw [hfixed, if_neg hg]
    simp

/-- Helper for Exercise 16-16.1-11: the rational class of the regular representation has
character `ψ₄`. -/
theorem rational_regular_class_character :
    finiteRepGrothendieckCharacter ℚ G [FDRep.of (leftRegular ℚ G)]₀ = ψ_ d₄ := by
  ext g
  rw [rational_index_four_permutation_character_apply (G := G) (hG := hG)]
  by_cases hg : g = 1
  · subst hg
    have hcard : Fintype.card G = 4 := by
      simpa using hG
    rw [finiteRepGrothendieckCharacter_class]
    rw [fdRep_ofMulAction_character_eq_ncard_fixedBy_field (G := G) (K := ℚ) (X := G)]
    simp [MulAction.mem_fixedBy, hcard]
  · rw [if_neg hg]
    rw [finiteRepGrothendieckCharacter_class]
    have hfixed : MulAction.fixedBy G g = (∅ : Set G) := by
      ext x
      constructor
      · intro hx
        rw [MulAction.mem_fixedBy] at hx
        have hx' := congrArg (fun y : G ↦ y * x⁻¹) hx
        exact hg (by simpa [mul_assoc] using hx')
      · intro hx
        simp at hx
    rw [fdRep_ofMulAction_character_eq_ncard_fixedBy_field (G := G) (K := ℚ) (X := G)]
    simp [hfixed]

end

end Exercise_16_16_1_11
