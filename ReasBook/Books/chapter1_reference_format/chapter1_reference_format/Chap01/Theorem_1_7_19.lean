import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u

namespace Set

/-- Theorem 1.7.19: a subset of a well-founded ordered type that contains every element whose
strict predecessors are already in the subset must be the whole type. -/
-- Proof sketch: prove `a ∈ A` for every `a` by well-founded induction on `<`, using the
-- induction hypothesis to show `Set.Iio a ⊆ A`, and then conclude `A = Set.univ` by extensionality.
theorem eq_univ_of_Iio_subset {α : Type u} [Preorder α] [WellFoundedLT α] (A : Set α)
    (hA : ∀ a, Iio a ⊆ A → a ∈ A) : A = univ := by
  refine eq_univ_of_forall fun a ↦ ?_
  refine wellFounded_lt.induction a fun a ih ↦ ?_
  exact hA a fun b hb ↦ ih b hb

end Set
