module

import Mathlib.Order.Defs.PartialOrder

universe u

/- Notation 3.5: In a partial order, `x ≤ y` is equivalent to
`x < y ∨ x = y`; Lean parses `y > x` as `x < y`, while the textbook's
chained phrase `x < y < z` is represented by `x < y ∧ y < z`. -/
#check le_iff_lt_or_eq
#check fun {α : Type u} [LT α] (x y : α) ↦ (y > x : Prop)
#check fun {α : Type u} [LT α] (x y z : α) ↦ x < y ∧ y < z
