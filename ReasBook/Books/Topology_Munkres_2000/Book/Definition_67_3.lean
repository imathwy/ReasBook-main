module

import Mathlib.Algebra.DirectSum.Module

public section

universe u v

variable {G : Type u} [AddCommGroup G] {J : Type v}
variable (Gα : J → AddSubgroup G)

section

variable [DecidableEq J]

/-
Definition 67.3. The group `G` is the direct sum of the subgroups `Gα` when they
generate `G` and every element has a unique expression as a finitely supported sum
of elements from the `Gα`. Mathlib's canonical predicate is `DirectSum.IsInternal Gα`.
-/
#check DirectSum.IsInternal Gα

end

/- For additive subgroups, the source conditions are independence and generation. -/
#check iSupIndep Gα ∧ (⨆ α, Gα α) = (⊤ : AddSubgroup G)
