module

public import Mathlib.Data.Set.«Card»

public section

/-- Exercise 1.8 (1): If `A` has two elements, then its power set has four
elements. -/
theorem powersetNcardEqFour {α : Type u} (A : Set α) (hcard : A.ncard = 2) :
    (𝒫 A).ncard = 4 := by
  -- The positive cardinality first supplies the finiteness needed by the power-set formula.
  have hne : A.ncard ≠ 0 := by
    rw [hcard]
    simp
  have hfinite : A.Finite := Set.finite_of_ncard_ne_zero hne
  -- Rewrite by the general power-set cardinality formula and evaluate the resulting power.
  rw [Set.ncard_powerset A hfinite, hcard]
  rfl

/-- Exercise 1.8 (2): If `A` has one element, then its power set has two
elements. -/
theorem powersetNcardEqTwo {α : Type u} (A : Set α) (hcard : A.ncard = 1) :
    (𝒫 A).ncard = 2 := by
  -- The nonzero cardinality ensures that `A` is finite.
  have hne : A.ncard ≠ 0 := by
    rw [hcard]
    simp
  have hfinite : A.Finite := Set.finite_of_ncard_ne_zero hne
  -- The power set has cardinality `2 ^ A.ncard`, which is two here.
  rw [Set.ncard_powerset A hfinite, hcard]
  rfl

/-- Exercise 1.8 (3): If `A` has three elements, then its power set has eight
elements. -/
theorem powersetNcardEqEight {α : Type u} (A : Set α) (hcard : A.ncard = 3) :
    (𝒫 A).ncard = 8 := by
  -- The prescribed positive cardinality gives the required finiteness hypothesis.
  have hne : A.ncard ≠ 0 := by
    rw [hcard]
    simp
  have hfinite : A.Finite := Set.finite_of_ncard_ne_zero hne
  -- Apply the general formula and compute `2 ^ 3`.
  rw [Set.ncard_powerset A hfinite, hcard]
  rfl

/-- Exercise 1.8 (4): If `A` has no elements, then its power set has one
element. -/
theorem powersetNcardEqOne {α : Type u} (A : Set α) (hA : A = ∅) :
    (𝒫 A).ncard = 1 := by
  -- Substitute the empty set so its power set reduces to the singleton containing `∅`.
  subst A
  simp

/- Exercise 1.8 (5): The formula `(𝒫 A).ncard = 2 ^ A.ncard` for finite
`A` explains the name “power set.” -/
#check Set.ncard_powerset
