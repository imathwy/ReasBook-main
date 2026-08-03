module

import Mathlib.Data.Set.Basic

universe u

/- Definition 1.2: Munkres writes `A ⊊ B` when `A` is a proper subset of `B`,
meaning that `A ⊆ B` and `A ≠ B`. In Lean, this strict inclusion is written
`A ⊂ B`. -/
#check fun {α : Type u} (A B : Set α) ↦ A ⊂ B
#check Set.ssubset_iff_subset_ne
