module

import Mathlib.Data.Set.Defs

universe u

/- Notation 1.10: If `B` is the set of elements `x ∈ X` for which `P x` holds,
Lean writes `B` as `{x ∈ X | P x}`. -/
#check fun {α : Type u} (X : Set α) (P : α → Prop) ↦ {x ∈ X | P x}
