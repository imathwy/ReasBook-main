module

import Mathlib.GroupTheory.Coset.Defs

universe u

open scoped Pointwise

/- Definition 2.99.3: For `x : G` and a subgroup `H` of `G`, the set
`x • (H : Set G)` is called the left coset of `H` in `G` represented by `x`. -/
#check fun {G : Type u} [Group G] (x : G) (H : Subgroup G) ↦ x • (H : Set G)

/- An element belongs to the left coset represented by `x` exactly when it has
the form `x * h` for some `h ∈ H`. -/
#check fun {G : Type u} [Group G] (x : G) (H : Subgroup G) (y : G) ↦
  (Set.mem_smul_set : y ∈ x • (H : Set G) ↔ ∃ h, h ∈ H ∧ x * h = y)
