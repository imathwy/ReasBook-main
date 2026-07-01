import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

variable {α : Type u} {β : Type v}
variable {X : Set α} {Y : Set β} {p : α × β}

/- Example 1.7.1: For sets `X` and `Y`, their Cartesian product is the canonical mathlib
operation `Set.prod`, written `X ×ˢ Y` in Lean. Its primitive owner is `Set.prod`, and the
elementwise description is the derived theorem `Set.mem_prod`. -/
recall Set.prod (X : Set α) (Y : Set β) : Set (α × β)

#check (Set.mem_prod : p ∈ X ×ˢ Y ↔ p.1 ∈ X ∧ p.2 ∈ Y)
