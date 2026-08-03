module

import Mathlib.Data.Real.Basic

/- Exercise 4.7 (1): For the canonical integer power on `ℝ`, defined by
`a ^ 0 = 1` and `a ^ (-n) = 1 / a ^ n`, powers with the same nonzero base
multiply by adding exponents. -/
#check fun (a : ℝ) (ha : a ≠ 0) (n m : ℤ) ↦ (zpow_add₀ ha n m).symm

/- Exercise 4.7 (2): For the canonical integer power on `ℝ`, defined by
`a ^ 0 = 1` and `a ^ (-n) = 1 / a ^ n`, iterating powers of a nonzero base
multiplies the exponents. The identity in fact holds without the nonzero
hypothesis. -/
#check fun (a : ℝ) (n m : ℤ) ↦ (zpow_mul a n m).symm

/- Exercise 4.7 (3): For the canonical integer power on `ℝ`, defined by
`a ^ 0 = 1` and `a ^ (-n) = 1 / a ^ n`, a power of a product of nonzero
reals is the product of their powers. The identity in fact holds without the
nonzero hypotheses. -/
#check fun (a b : ℝ) (m : ℤ) ↦ (mul_zpow a b m).symm
