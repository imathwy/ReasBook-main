module

import Mathlib.Algebra.Group.Pointwise.Set.Basic

universe u

open scoped Pointwise

/- Notation 2.99.1: For subsets `A B : Set G`, the product `A * B` is the set
of products `a * b` with `a ∈ A` and `b ∈ B`, and `A⁻¹` is the set of inverses
of elements of `A`. -/
#check fun {G : Type u} [Mul G] (A B : Set G) ↦ A * B
#check fun {G : Type u} [InvolutiveInv G] (A : Set G) ↦ A⁻¹
#check Set.mem_mul
#check Set.image_inv_eq_inv
