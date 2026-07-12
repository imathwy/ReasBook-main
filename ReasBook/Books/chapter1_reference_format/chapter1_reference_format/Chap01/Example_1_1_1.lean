import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

variable {α : Type u} {β : Type v}
variable {s : Set α} {t : Set β} {p : α × β}

/- Example 1.1.1: For sets `X` and `Y`, the Cartesian product is the canonical mathlib operation
`Set.prod`, written `X ×ˢ Y` in Lean. Its primitive owner is `Set.prod`, and the elementwise
description is the derived theorem `Set.mem_prod`. -/
recall Set.prod (s : Set α) (t : Set β) : Set (α × β)

#check (Set.mem_prod : p ∈ s ×ˢ t ↔ p.1 ∈ s ∧ p.2 ∈ t)
