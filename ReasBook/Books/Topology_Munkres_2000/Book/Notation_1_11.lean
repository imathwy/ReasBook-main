module

import Mathlib.Data.Set.Defs

universe u

/- Notation 1.11: For `A = {a, b, c}`, distinguish the element `a : α`
from the singleton `{a} : Set α`. Thus `a ∈ A`, `{a} ⊆ A`, and
`{a} ∈ 𝒫 A` are well-typed statements; `{a} ∈ A` and `a ⊆ A` confuse these
two type levels and are not well-typed. -/
#check fun {α : Type u} (a b c : α) ↦ a ∈ ({a, b, c} : Set α)
#check fun {α : Type u} (a b c : α) ↦ ({a} : Set α) ⊆ ({a, b, c} : Set α)
#check fun {α : Type u} (a b c : α) ↦ ({a} : Set α) ∈ 𝒫 ({a, b, c} : Set α)
