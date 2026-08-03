module

import Mathlib.Data.Set.Defs

public section

/- Notation 1.6: `{x : α | p x}` denotes the set of all `x` such that `p x`. -/
#check setOf

universe u

variable {α : Type u} (p : α → Prop)

#check ({x : α | p x} : Set α)
