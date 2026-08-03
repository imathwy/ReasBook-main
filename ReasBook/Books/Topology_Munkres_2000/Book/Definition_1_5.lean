module

import Mathlib.Data.Set.Basic

public section

universe u

variable {α : Type u}

/- Definition 1.5: The empty set `∅` is the set having no elements. -/
#check (∅ : Set α)
#check Set.notMem_empty
