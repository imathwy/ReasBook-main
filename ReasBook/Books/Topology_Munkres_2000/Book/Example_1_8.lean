module

public import Mathlib.Order.SetNotation

public section

/-- Example 1.8: The two parenthesized mixtures of union and intersection can differ. -/
theorem setOperationParenthesesCanDiffer :
    ∃ A B C : Set Bool, A ∪ (B ∩ C) ≠ (A ∪ B) ∩ C := by
  refine ⟨Set.univ, ∅, ∅, ?_⟩
  intro h
  have hmem : true ∈ Set.univ ∪ ((∅ : Set Bool) ∩ ∅) := Or.inl trivial
  rw [h] at hmem
  exact hmem.2
