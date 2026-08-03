module

import Mathlib.Algebra.Group.Defs

universe u

/- Notation 67.1: In an abelian group written additively, `0` denotes the
identity, `-x` denotes the inverse of `x`, and `n • x` denotes the `n`-fold sum
of `x`. -/
#check fun {G : Type u} [AddCommGroup G] ↦ (0 : G)
#check fun {G : Type u} [AddCommGroup G] (x : G) ↦ -x
#check fun {G : Type u} [AddCommGroup G] (n : ℕ) (x : G) ↦ n • x
