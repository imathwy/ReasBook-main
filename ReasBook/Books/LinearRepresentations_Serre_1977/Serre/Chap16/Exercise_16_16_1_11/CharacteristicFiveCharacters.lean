import LinearRepresentations_Serre_1977.Chap16.Exercise_16_16_1_11.Common

noncomputable section

open CategoryTheory
open Representation
open scoped Representation SubgroupInduction

namespace Exercise_16_16_1_11

section CharacteristicFiveCharacters

variable {G : Type} [Group G] [Finite G] [IsCyclic G]

local instance characteristicFiveCharactersFintype : Fintype G := Fintype.ofFinite G
local instance characteristicFiveCharactersCommGroup : CommGroup G := IsCyclic.commGroup

local notation "DivisorIndex" => { d : ℕ // d ∣ Nat.card G }

/-- Helper for Exercise 16-16.1-11: the canonical subgroup of a finite cyclic group obtained from
the `d`-th power map. This is the source-facing subgroup denoted `G_d` in Serre. -/
noncomputable def cyclicSubgroupOfIndex_char5
    (d : DivisorIndex) : Subgroup G :=
  (powMonoidHom d.1 : G →* G).range

local prefix:max "G_ " => cyclicSubgroupOfIndex_char5

/-- Helper for Exercise 16-16.1-11: the canonical subgroup `G_d` has index `d`. -/
theorem cyclicSubgroupOfIndex_index_char5
    (d : DivisorIndex) :
    (G_ d).index = d.1 := by
  have hdvd : d.1 ∣ Fintype.card G := by
    simpa [Nat.card_eq_fintype_card] using d.2
  simpa [cyclicSubgroupOfIndex_char5, Nat.gcd_eq_right hdvd] using
    (IsCyclic.index_powMonoidHom_range (G := G) d.1)

attribute [local instance] Classical.decEq Classical.propDecidable

abbrev quotientPermutationCharacterRingOverField
    (k : Type) [Field k] (H : Subgroup G) : R[k](G) :=
  finiteRepGrothendieckCharacter k G [FDRep.of (ofMulAction k G (G ⧸ H))]₀

abbrev regularCharacterRingOverField
    (k : Type) [Field k] : R[k](G) :=
  finiteRepGrothendieckCharacter k G [FDRep.of (leftRegular k G)]₀

variable (k : Type) [Field k] [CharP k 5] (hG : Nat.card G = 4)

local notation "d₂" => cyclicOrderFourDivisorIndexTwo hG

/-- Helper for Exercise 16-16.1-11: the character of a permutation representation counts the
fixed points of the acting element. -/
theorem fdRep_ofMulAction_character_eq_ncard_fixedBy
    (X : Type) [MulAction G X] [Finite X] (g : G) :
    (FDRep.of (ofMulAction k G X)).character g = ↑(MulAction.fixedBy X g).ncard := by
  classical
  letI : Fintype X := Fintype.ofFinite X
  change (ofMulAction k G X).character g = ↑(MulAction.fixedBy X g).ncard
  calc
    (ofMulAction k G X).character g
      = Matrix.trace
          (LinearMap.toMatrix Finsupp.basisSingleOne Finsupp.basisSingleOne
            ((ofMulAction k G X) g)) := by
            rw [Representation.character,
              LinearMap.trace_eq_matrix_trace k Finsupp.basisSingleOne]
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

/-- Helper for Exercise 16-16.1-11: on the quotient by the unique index-`2` subgroup, an element
fixes a coset exactly when it already lies in that subgroup. -/
theorem quotient_index_two_fixed_iff_mem
    (g : G) (x : G ⧸ G_ d₂) :
    x ∈ MulAction.fixedBy (G ⧸ G_ d₂) g ↔ g ∈ G_ d₂ := by
  rcases Quotient.exists_rep x with ⟨a, rfl⟩
  rw [MulAction.mem_fixedBy]
  change QuotientGroup.mk (g * a) = QuotientGroup.mk a ↔ g ∈ G_ d₂
  rw [QuotientGroup.eq_iff_div_mem]
  simp [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]

/-- Helper for Exercise 16-16.1-11: the quotient by the unique index-`2` subgroup has cardinality
`2`. -/
theorem quotient_index_two_card :
    Nat.card (G ⧸ G_ d₂) = 2 := by
  simpa [Subgroup.index_eq_card] using cyclicSubgroupOfIndex_index_char5 (G := G) (d := d₂)

/-- Helper for Exercise 16-16.1-11: the quotient-permutation character attached to the unique
index-`2` subgroup takes the value `2` on that subgroup and `0` off it. -/
theorem quotient_permutation_character_index_two_apply
    (g : G) :
    (quotientPermutationCharacterRingOverField k (G_ d₂) : G → k) g =
      if g ∈ G_ d₂ then 2 else 0 := by
  rw [quotientPermutationCharacterRingOverField, finiteRepGrothendieckCharacter_class]
  rw [fdRep_ofMulAction_character_eq_ncard_fixedBy (G := G) (k := k) (X := G ⧸ G_ d₂)]
  by_cases hg : g ∈ G_ d₂
  · have hfixed : MulAction.fixedBy (G ⧸ G_ d₂) g = Set.univ := by
      ext x
      constructor
      · intro _
        simp
      · intro _
        exact (quotient_index_two_fixed_iff_mem (G := G) (hG := hG) (g := g) (x := x)).2 hg
    rw [hfixed]
    have hcardQ : Fintype.card (G ⧸ G_ d₂) = 2 := by
      simpa [Nat.card_eq_fintype_card] using quotient_index_two_card (G := G) (hG := hG)
    rw [if_pos hg]
    norm_num [hcardQ]
  · have hfixed : MulAction.fixedBy (G ⧸ G_ d₂) g = (∅ : Set (G ⧸ G_ d₂)) := by
      ext x
      constructor
      · intro hx
        exact False.elim (hg ((quotient_index_two_fixed_iff_mem (G := G) (hG := hG) (g := g)
          (x := x)).1 hx))
      · intro hx
        simp at hx
    rw [hfixed]
    rw [if_neg hg]
    simp

/-- The canonical quadratic characteristic-`5` character of a cyclic group of order `4`,
determined by the unique index-`2` subgroup `G_2`, viewed in `R[k](G)`. -/
def cyclicOrderFourQuadraticCharacter : R[k](G) :=
  quotientPermutationCharacterRingOverField k (G_ d₂) - 1

@[simp] theorem cyclicOrderFourQuadraticCharacter_apply
    (g : G) :
    (cyclicOrderFourQuadraticCharacter (G := G) k hG : G → k) g =
      if g ∈ G_ d₂ then 1 else -1 := by
  change (quotientPermutationCharacterRingOverField k (G_ d₂) : G → k) g - 1 =
    if g ∈ G_ d₂ then 1 else -1
  rw [quotient_permutation_character_index_two_apply (G := G) (k := k) (hG := hG)]
  by_cases hg : g ∈ G_ d₂
  · norm_num [hg]
  · simp [hg]

/-- The canonical symmetric sum of the two faithful degree-one characteristic-`5` characters of a
cyclic group of order `4`, viewed in `R[k](G)`. Pointwise it takes the values `2` at `1`, `-2`
at the nontrivial element of the index-`2` subgroup `G_2`, and `0` on the elements of order
`4`. -/
def cyclicOrderFourFaithfulCharacterSum : R[k](G) :=
  regularCharacterRingOverField k - quotientPermutationCharacterRingOverField k (G_ d₂)

@[simp] theorem cyclicOrderFourFaithfulCharacterSum_apply
    (g : G) :
    (cyclicOrderFourFaithfulCharacterSum (G := G) k hG : G → k) g =
      if g = 1 then 2 else if g ∈ G_ d₂ then -2 else 0 := by
  change (regularCharacterRingOverField k : G → k) g -
      (quotientPermutationCharacterRingOverField k (G_ d₂) : G → k) g =
    if g = 1 then 2 else if g ∈ G_ d₂ then -2 else 0
  by_cases hg1 : g = 1
  · subst hg1
    have hcard : Fintype.card G = 4 := by
      simpa using hG
    rw [quotient_permutation_character_index_two_apply (G := G) (k := k) (hG := hG)]
    rw [regularCharacterRingOverField, finiteRepGrothendieckCharacter_class,
      fdRep_ofMulAction_character_eq_ncard_fixedBy (G := G) (k := k) (X := G)]
    simp [MulAction.mem_fixedBy, hcard]
    ring
  · rw [quotient_permutation_character_index_two_apply (G := G) (k := k) (hG := hG)]
    have hfixed : MulAction.fixedBy G g = (∅ : Set G) := by
      ext x
      constructor
      · intro hx
        rw [MulAction.mem_fixedBy] at hx
        have hx' := congrArg (fun y : G ↦ y * x⁻¹) hx
        exact hg1 (by simpa [mul_assoc] using hx')
      · intro hx
        simp at hx
    rw [regularCharacterRingOverField, finiteRepGrothendieckCharacter_class]
    rw [fdRep_ofMulAction_character_eq_ncard_fixedBy (G := G) (k := k) (X := G)]
    simp [hfixed, hg1]
    by_cases hg : g ∈ G_ d₂
    · simp [hg1, hg]
    · simp [hg1, hg]

/-- Helper for Exercise 16-16.1-11: the quadratic characteristic-`5` character is unchanged by
inversion. -/
theorem cyclicOrderFourQuadraticCharacter_inv
    (g : G) :
    (cyclicOrderFourQuadraticCharacter (G := G) k hG : G → k) g⁻¹ =
      (cyclicOrderFourQuadraticCharacter (G := G) k hG : G → k) g := by
  simp [cyclicOrderFourQuadraticCharacter_apply, Subgroup.inv_mem_iff]

/-- Helper for Exercise 16-16.1-11: the symmetric faithful characteristic-`5` character sum is
unchanged by inversion. -/
theorem cyclicOrderFourFaithfulCharacterSum_inv
    (g : G) :
    (cyclicOrderFourFaithfulCharacterSum (G := G) k hG : G → k) g⁻¹ =
      (cyclicOrderFourFaithfulCharacterSum (G := G) k hG : G → k) g := by
  by_cases hg1 : g = 1
  · subst hg1
    simp [cyclicOrderFourFaithfulCharacterSum_apply]
  · have hginv1 : g⁻¹ ≠ 1 := by
      intro hginv1
      apply hg1
      simpa using inv_eq_one.mp hginv1
    by_cases hg : g ∈ G_ d₂
    · have hginv : g⁻¹ ∈ G_ d₂ := by
        simpa using hg
      simp [cyclicOrderFourFaithfulCharacterSum_apply, hg1, hginv1, hg, hginv]
    · have hginv : g⁻¹ ∉ G_ d₂ := by
        simpa [Subgroup.inv_mem_iff] using hg
      simp [cyclicOrderFourFaithfulCharacterSum_apply, hg1, hginv1, hg, hginv]

end CharacteristicFiveCharacters

end Exercise_16_16_1_11
