import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

/- The remark also uses the standard commutative ring structure on the integers. -/
#check (inferInstance : CommRing ℤ)

/- Remark 1.1.36: the integers form an integral domain. The absolute-value argument in the text
is one proof of this canonical domain structure. -/
#check (inferInstance : IsDomain ℤ)

/- As a derived consequence, multiplication in `ℤ` has no nontrivial zero divisors. -/
#check Int.eq_zero_or_eq_zero_of_mul_eq_zero
