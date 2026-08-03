module

import Mathlib.Data.Set.Basic

variable {α : Type*}

/- Definition 1.11: The difference `A - B`, written `A \\ B` in Lean, consists
of the elements of `A` that are not in `B`; it is also the complement of `B`
relative to `A`. -/
#check fun A B : Set α ↦ A \ B
#check Set.mem_sdiff
