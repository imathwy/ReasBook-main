import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

/- Theorem I.3-extra-3: `Complex.range_exp_mul_I` states that the homomorphism
`y ↦ exp (y * I)` maps `ℝ` onto the complex unit circle. -/
#check Complex.range_exp_mul_I

/-- The kernel of the exponential parametrization of the unit circle consists exactly of the
integral multiples of `2 * π`. -/
theorem complex_exp_real_mul_I_eq_one_iff {y : ℝ} :
    Complex.exp (y * Complex.I) = 1 ↔ ∃ n : ℤ, y = n * (2 * Real.pi) := by
  rw [← Circle.coe_exp, Circle.coe_eq_one]
  exact Circle.exp_eq_one
