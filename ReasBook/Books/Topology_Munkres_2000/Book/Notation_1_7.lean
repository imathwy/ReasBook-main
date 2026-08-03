module

import Mathlib.Data.Set.Basic

/- Notation 1.7: The word “or” is inclusive, so `x ∈ A ∪ B` means that
`x ∈ A`, or `x ∈ B`, or both; equivalently, `A ∪ B = {x | x ∈ A ∨ x ∈ B}`. -/
#check Or
#check Set.mem_union
#check Set.union_def
