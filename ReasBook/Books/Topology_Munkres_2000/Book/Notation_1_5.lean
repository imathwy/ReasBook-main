module

import Mathlib.Data.Set.Insert

universe u

variable {α : Type u} (a b c : α)

/- Notation 1.5: A set consisting of the elements `a`, `b`, and `c` is written
`{a, b, c}`. -/
#check ({a, b, c} : Set α)
