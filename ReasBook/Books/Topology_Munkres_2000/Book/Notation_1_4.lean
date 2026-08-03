module

import Mathlib.Data.Set.Basic

universe u

/- Notation 1.4: The relations `A ⊆ B` and `A ⊂ B` are called inclusion and
proper inclusion, respectively. The notation `B ⊇ A` is read “`B` contains
`A`.” -/
#check fun {α : Type u} (A B : Set α) ↦ A ⊆ B
#check fun {α : Type u} (A B : Set α) ↦ A ⊂ B
#check fun {α : Type u} (A B : Set α) ↦ B ⊇ A
