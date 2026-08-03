module

import Mathlib.Algebra.Group.Defs

universe u

/- Notation 68.1: For a group `G`, not necessarily abelian, `1` denotes the
identity, `x⁻¹` denotes the inverse of `x`, `x ^ n` denotes the `n`-fold product
of `x`, `x ^ (-(n : ℤ))` denotes the `n`-fold product of `x⁻¹`, and
`x ^ (0 : ℤ)` denotes `1`. -/
#check fun {G : Type u} [Group G] ↦ (1 : G)
#check fun {G : Type u} [Group G] (x : G) ↦ x⁻¹
#check fun {G : Type u} [Group G] (x : G) (n : ℕ) ↦ x ^ n
#check fun {G : Type u} [Group G] (x : G) (n : ℕ) ↦ x ^ (-(n : ℤ))
#check fun {G : Type u} [Group G] (x : G) ↦ x ^ (0 : ℤ)
