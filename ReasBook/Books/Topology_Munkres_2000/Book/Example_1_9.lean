module

import Mathlib.Data.Set.Defs

universe u

/- Example 1.9: elements of a set may themselves be sets. In Lean, a collection
`𝒜` of sets of objects of type `α` has type `Set (Set α)`, and `A ∈ 𝒜` says
that the set `A` belongs to that collection. -/
#check fun {α : Type u} (𝒜 : Set (Set α)) (A : Set α) ↦ A ∈ 𝒜
