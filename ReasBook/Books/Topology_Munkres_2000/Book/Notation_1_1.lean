module

import Mathlib.Data.Set.Defs

universe u

/- Notation 1.1: For `a : α` and `A : Set α`, the expression `a ∈ A` states
that `a` belongs to `A`, while `a ∉ A` states that it does not. -/
#check fun {α : Type u} (a : α) (A : Set α) ↦ a ∈ A
#check fun {α : Type u} (a : α) (A : Set α) ↦ a ∉ A
