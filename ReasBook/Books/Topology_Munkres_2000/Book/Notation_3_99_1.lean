module

import Init

public section

universe u v

/- Notation 3.99.1: Lean represents the net `(x_α)_{α ∈ J}` directly by its
underlying function `x : J → X`. Thus the term `x_α` is written `x α`, and
when the index type is understood, the net `(x_α)` is simply `x`. -/
#check fun {J : Type u} {X : Type v} (x : J → X) (α : J) ↦ x α
#check fun {J : Type u} {X : Type v} (x : J → X) ↦ x
