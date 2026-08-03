module

import Mathlib.Data.Set.Disjoint

universe u

/- Remark 17.6: A set `A` intersects a set `B` when their intersection
`A ∩ B` is nonempty. -/
#check fun {α : Type u} (A B : Set α) ↦ (A ∩ B).Nonempty

-- This terminology is equivalent to saying that the sets are not disjoint.
#check Set.not_disjoint_iff_nonempty_inter
