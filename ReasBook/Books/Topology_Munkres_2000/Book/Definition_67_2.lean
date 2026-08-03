module

import Mathlib.Algebra.Group.Subgroup.Lattice

public section

universe u v

variable {G : Type u} [AddCommGroup G] {J : Type v}
variable (Gα : J → AddSubgroup G)

/-
Definition 67.2. Saying that `G` is the sum of the subgroups `Gα` is terminology for
the generation condition `(⨆ α, Gα α) = ⊤`. Mathlib represents the subgroup sum by
the supremum `⨆ α, Gα α`; the source writes this equality as `G = ∑ α, Gα α`, or as
`G = G₁ + ⋯ + Gₙ` for a finite family.
-/
#check (⨆ α, Gα α) = (⊤ : AddSubgroup G)
