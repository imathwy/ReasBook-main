module

import Mathlib.Data.Set.Defs

public section

universe u

variable (α : Type u)

/- Example 1.10: A set whose elements are sets of objects of type `α` is called
a collection of sets and has the canonical Lean type `Set (Set α)`. -/
#check Set (Set α)
