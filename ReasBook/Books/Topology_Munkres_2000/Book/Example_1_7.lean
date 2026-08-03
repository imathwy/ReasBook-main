module

import Mathlib.Data.Set.Defs

universe u

/- Example 1.7: for every `x ∈ A`, the statement `P x` holds. -/
#check fun {X : Type u} (A : Set X) (P : X → Prop) ↦ ∀ x ∈ A, P x
