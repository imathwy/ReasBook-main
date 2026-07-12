import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

variable (A : Type u) [CommRing A]

-- Semantic recall: `lean_leansearch` returned unrelated `Seminormed*` results, and local search
-- found no existing ring owner for seminormality or absolute weak normality in this project.
-- The source-facing reusable API is therefore introduced directly as ring-property classes.

/-- Definition 29.47.1 (1): a ring `A` is seminormal if whenever `x^3 = y^2` in `A`, there is a
unique `a : A` such that `x = a^2` and `y = a^3`. -/
@[stacks 0EUL]
class SeminormalRing : Prop where
  existsUnique_sq_cube_of_cube_eq_sq :
    ∀ ⦃x y : A⦄, x ^ 3 = y ^ 2 → ∃! a : A, x = a ^ 2 ∧ y = a ^ 3

/-- Definition 29.47.1 (2): a ring `A` is absolutely weakly normal if it is seminormal and for
every prime number `p` and all `x, y : A` with `(p : A)^p * x = y^p`, there is a unique `a : A`
such that `x = a^p` and `y = (p : A) * a`. -/
@[stacks 0EUL]
class AbsolutelyWeaklyNormalRing : Prop extends SeminormalRing A where
  existsUnique_pow_of_prime_pow_mul_eq_pow :
    ∀ ⦃p : ℕ⦄, Nat.Prime p →
      ∀ ⦃x y : A⦄, ((p : A) ^ p) * x = y ^ p → ∃! a : A, x = a ^ p ∧ y = (p : A) * a

end
