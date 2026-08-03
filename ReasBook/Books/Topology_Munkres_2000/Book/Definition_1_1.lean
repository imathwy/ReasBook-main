module

import Mathlib.Data.Set.Basic

universe u

/- Definition 1.1: For sets `A B : Set α`, the relation `A ⊆ B` means that
every element of `A` is also an element of `B`. -/
#check fun {α : Type u} (A B : Set α) ↦ A ⊆ B
#check Set.subset_def
