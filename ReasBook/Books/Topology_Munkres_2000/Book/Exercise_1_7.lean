module

public import Mathlib.Order.SetNotation

public section

/-- Exercise 1.7, part (1): The elements in `A` that belong to `B` or `C` form
`A ∩ (B ∪ C)`. -/
theorem setOf_mem_and_mem_or_eq {α : Type u} (A B C : Set α) :
    {x | x ∈ A ∧ (x ∈ B ∨ x ∈ C)} = A ∩ (B ∪ C) := by
  -- Extensionality reduces the set identity to the identical membership formula.
  ext x
  rfl

/-- Exercise 1.7, part (2): The elements belonging to both `A` and `B`, or belonging
to `C`, form `(A ∩ B) ∪ C`. -/
theorem setOf_mem_inter_or_mem_eq {α : Type u} (A B C : Set α) :
    {x | (x ∈ A ∧ x ∈ B) ∨ x ∈ C} = (A ∩ B) ∪ C := by
  -- Membership in the intersection and union unfolds to the set-builder predicate.
  ext x
  rfl

/-- Exercise 1.7, part (3): The elements of `A` for which membership in `B` implies
membership in `C` form `A \ (B \ C)`. -/
theorem setOf_mem_and_imp_mem_eq {α : Type u} (A B C : Set α) :
    {x | x ∈ A ∧ (x ∈ B → x ∈ C)} = A \ (B \ C) := by
  classical
  -- Difference membership excludes exactly a counterexample to the implication.
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_sdiff]
  constructor
  · rintro ⟨hxA, hBC⟩
    refine ⟨hxA, ?_⟩
    rintro ⟨hxB, hxC⟩
    exact hxC (hBC hxB)
  · rintro ⟨hxA, hcounterexample⟩
    refine ⟨hxA, ?_⟩
    intro hxB
    by_contra hxC
    exact hcounterexample ⟨hxB, hxC⟩
