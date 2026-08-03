module

import Mathlib.Data.Rel

universe u v

/- Definition 2.4: For sets `A : Set α` and `B : Set β`, a function with
domain `A` and specified target set `B` is canonically a term of type `A → B`.
The subtype codomain records that every assigned value belongs to `B`.
Munkres calls `B` the range; in Lean terminology it is the codomain, while
`Set.range` denotes the image set. -/
#check (fun {α : Type u} {β : Type v} (A : Set α) (B : Set β) ↦ A → B)

-- The rule of assignment underlying a Lean function is its graph relation.
#check Function.graph

-- The image set of a function is expressed using `Set.range`.
#check Set.range
