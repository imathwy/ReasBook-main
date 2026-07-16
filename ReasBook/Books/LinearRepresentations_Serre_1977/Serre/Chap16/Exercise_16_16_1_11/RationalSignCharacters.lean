import LinearRepresentations_Serre_1977.Serre.Chap16.Exercise_16_16_1_11.RationalInfrastructure

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

local instance rationalSignCharactersFintype : Fintype G := Fintype.ofFinite G
local instance rationalSignCharactersCommGroup : CommGroup G := IsCyclic.commGroup
local instance rationalSignCharactersIsDomain : IsDomain A := (IsFractionRing.injective A ℚ).isDomain
attribute [local instance] Classical.decEq Classical.propDecidable

local notation "d₂" => cyclicOrderFourDivisorIndexTwo hG
local notation "d₄" => cyclicOrderFourDivisorIndexFour hG
local prefix:max "G_ " => cyclicSubgroupOfIndex

-- `unitCharacterToRepresentation`, `unitCharacterToRepresentation_character_apply`,
-- `representation_isIrreducible_of_finrank_eq_one`, and
-- `unitCharacterToRepresentation_isIrreducible` are provided by the aggregator
-- `Serre.Chap16.Exercise_16_16_1_11` (imported transitively) and reused here.

attribute [local instance] Classical.decEq Classical.propDecidable

/-- Helper for Exercise 16-16.1-11: the sign character on `ZMod 2` is multiplicative because the
parity exponents add modulo `2`. -/
theorem zmod2_sign_mul
    (a b : ZMod 2) :
    (-1 : ℚˣ) ^ (a + b).val =
      (-1 : ℚˣ) ^ a.val * (-1 : ℚˣ) ^ b.val := by
  fin_cases a
  · fin_cases b
    · change (-1 : ℚˣ) ^ 0 = (-1 : ℚˣ) ^ 0 * (-1 : ℚˣ) ^ 0
      norm_num
    · change (-1 : ℚˣ) ^ 1 = (-1 : ℚˣ) ^ 0 * (-1 : ℚˣ) ^ 1
      norm_num
  · fin_cases b
    · change (-1 : ℚˣ) ^ 1 = (-1 : ℚˣ) ^ 1 * (-1 : ℚˣ) ^ 0
      norm_num
    · change (-1 : ℚˣ) ^ 0 = (-1 : ℚˣ) ^ 1 * (-1 : ℚˣ) ^ 1
      norm_num

/-- Helper for Exercise 16-16.1-11: the canonical sign character on the cyclic group of order
`2`, written on `Multiplicative (ZMod 2)`. -/
def zmod2Sign : Multiplicative (ZMod 2) →* ℚˣ where
  toFun z := (-1 : ℚˣ) ^ (Multiplicative.toAdd z).val
  map_one' := by
    simp
  map_mul' a b := by
    simpa using zmod2_sign_mul (Multiplicative.toAdd a) (Multiplicative.toAdd b)

/-- Helper for Exercise 16-16.1-11: reduction modulo `2` records the parity of an exponent in
`Multiplicative (ZMod 4)`. -/
def zmod4Parity : Multiplicative (ZMod 4) →* Multiplicative (ZMod 2) :=
  AddMonoidHom.toMultiplicative
    ((ZMod.castHom (by decide : 2 ∣ 4) (ZMod 2)).toAddMonoidHom)

/-- Helper for Exercise 16-16.1-11: the explicit quadratic sign character on
`Multiplicative (ZMod 4)`. -/
def zmod4Sign : Multiplicative (ZMod 4) →* ℚˣ :=
  zmod2Sign.comp zmod4Parity

/-- Helper for Exercise 16-16.1-11: on `Multiplicative (ZMod 4)`, the sign character is `1`
exactly on squares. -/
theorem zmod4Sign_eq_one_iff_isSquare
    (z : Multiplicative (ZMod 4)) :
    zmod4Sign z = 1 ↔ ∃ x : Multiplicative (ZMod 4), x ^ 2 = z := by
  fin_cases z <;> decide

/-- Helper for Exercise 16-16.1-11: the explicit rational quadratic sign character of a cyclic
group of order `4`, obtained by transporting the parity character on `ZMod 4`. -/
def quadraticSignCharacter : G →* ℚˣ := by
  let g0 : G := Classical.choose (IsCyclic.exists_generator (α := G))
  have hg0_gen : ∀ x : G, x ∈ Subgroup.zpowers g0 :=
    Classical.choose_spec (IsCyclic.exists_generator (α := G))
  let eG : Multiplicative (ZMod 4) ≃* G := zmodMulEquivOfGenerator hg0_gen hG
  exact zmod4Sign.comp eG.symm.toMonoidHom

/-- Helper for Exercise 16-16.1-11: the rational quadratic sign character is trivial exactly on
the unique index-`2` subgroup `G_2`. -/
theorem quadraticSignCharacter_eq_one_iff_mem
    (g : G) :
    quadraticSignCharacter (G := G) hG g = 1 ↔
      g ∈ G_ d₂ := by
  let g0 : G := Classical.choose (IsCyclic.exists_generator (α := G))
  have hg0_gen : ∀ x : G, x ∈ Subgroup.zpowers g0 :=
    Classical.choose_spec (IsCyclic.exists_generator (α := G))
  let eG : Multiplicative (ZMod 4) ≃* G := zmodMulEquivOfGenerator hg0_gen hG
  change zmod4Sign (eG.symm g) = 1 ↔ g ∈ G_ d₂
  rw [zmod4Sign_eq_one_iff_isSquare]
  constructor
  · rintro ⟨x, hx⟩
    simpa [cyclicSubgroupOfIndex] using
      ⟨eG x, by simpa using congrArg eG hx⟩
  · intro hg
    rcases (by
        simpa [cyclicSubgroupOfIndex] using
          hg : ∃ x : G, x ^ 2 = g) with ⟨x, hx⟩
    exact ⟨eG.symm x, by simpa using congrArg eG.symm hx⟩

/-- Helper for Exercise 16-16.1-11: the explicit rational quadratic sign character takes the
values `1` on `G_2` and `-1` off `G_2`. -/
theorem quadraticSignCharacter_apply
    (g : G) :
    (quadraticSignCharacter (G := G) hG g : ℚ) =
      if g ∈ G_ d₂ then 1 else -1 := by
  let H : Subgroup G := G_ d₂
  by_cases hg : g ∈ H
  · have hq : quadraticSignCharacter (G := G) hG g = 1 := by
      simpa [H] using (quadraticSignCharacter_eq_one_iff_mem (G := G) (hG := hG) g).2 hg
    simp [H, hg, hq]
  · have hneq1 : (quadraticSignCharacter (G := G) hG g : ℚ) ≠ 1 := by
      intro h1
      apply hg
      exact
        (quadraticSignCharacter_eq_one_iff_mem (G := G) (hG := hG) g).1
          (Units.ext h1)
    have hsqUnits : (quadraticSignCharacter (G := G) hG g) ^ 2 = 1 := by
      have hg2 : g ^ 2 ∈ H := by
        simpa [H, cyclicSubgroupOfIndex] using ⟨g, rfl⟩
      simpa [H] using
        (quadraticSignCharacter_eq_one_iff_mem (G := G) (hG := hG) (g ^ 2)).2 hg2
    have hsq : ((quadraticSignCharacter (G := G) hG g : ℚ) ^ 2) = 1 := by
      exact congrArg (fun u : ℚˣ ↦ (u : ℚ)) hsqUnits
    have hneg : (quadraticSignCharacter (G := G) hG g : ℚ) = -1 :=
      (sq_eq_one_iff.mp hsq).resolve_left hneq1
    simp [H, hg, hneg]

/-- Helper for Exercise 16-16.1-11: the explicit rational sign line has kernel `G₂`. -/
theorem quadratic_sign_line_kernel_eq_index_two :
    (unitCharacterToRepresentation (quadraticSignCharacter (G := G) hG)).ker = G_ d₂ := by
  ext x
  constructor
  · intro hx
    have hxeval := congrArg (fun f : ℚ →ₗ[ℚ] ℚ ↦ f 1) hx
    exact
      (quadraticSignCharacter_eq_one_iff_mem (G := G) (hG := hG) x).1
        (by simpa [unitCharacterToRepresentation, LinearMap.lsmul_apply] using hxeval)
  · intro hx
    ext t
    have hx' :
        (quadraticSignCharacter (G := G) hG x : ℚ) = 1 := by
      simpa using
        congrArg (fun u : ℚˣ ↦ (u : ℚ))
          ((quadraticSignCharacter_eq_one_iff_mem (G := G) (hG := hG) x).2 hx)
    simp [unitCharacterToRepresentation, LinearMap.lsmul_apply, hx']

/-- Helper for Exercise 16-16.1-11: transport a representation across a linear equivalence. -/
def transport_representation
    {K : Type} [Field K] {H : Type} [Group H]
    {V : Type} {W : Type}
    [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    (e : V ≃ₗ[K] W) (ρ : Representation K H V) : Representation K H W where
  toFun g := e.conj (ρ g)
  map_one' := by
    ext x
    simp [LinearEquiv.conj_apply_apply]
  map_mul' g₁ g₂ := by
    ext x
    simp [LinearEquiv.conj_apply_apply]

/-- Helper for Exercise 16-16.1-11: an explicit intertwining identity determines the transported
action. -/
theorem transport_representation_apply_eq_of_intertwines
    {K : Type} [Field K] {H : Type} [Group H]
    {V : Type} {W : Type}
    [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    (e : W ≃ₗ[K] V) (ρ : Representation K H V) (g : H) (f : W →ₗ[K] W)
    (h : ρ g ∘ₗ e.toLinearMap = e.toLinearMap ∘ₗ f) :
    transport_representation e.symm ρ g = f := by
  ext x
  change e.symm ((ρ g ∘ₗ e.toLinearMap) x) = f x
  rw [h]
  simp

end

end Exercise_16_16_1_11
