module

public import Mathlib.SetTheory.Cardinal.Order

public section

universe u

/-- Exercise 10.11: For any two types, their cardinalities are equal, or one is
strictly smaller than the other. -/
theorem cardinalityTrichotomy (A B : Type u) :
    Cardinal.mk A = Cardinal.mk B ∨
      Cardinal.mk A < Cardinal.mk B ∨ Cardinal.mk B < Cardinal.mk A := by
  -- Cardinal numbers form a linear order, so compare the two cardinalities.
  rcases lt_trichotomy (Cardinal.mk A) (Cardinal.mk B) with h | h | h
  · -- A strict inequality gives the left branch of the nested alternative.
    exact Or.inr (Or.inl h)
  · -- Equality is the first alternative in the target statement.
    exact Or.inl h
  · -- The reverse strict inequality gives the final alternative.
    exact Or.inr (Or.inr h)
