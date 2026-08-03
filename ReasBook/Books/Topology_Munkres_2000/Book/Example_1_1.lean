module

public import Mathlib.Data.Real.Basic

public section

/-- Example 1.1: If a real number `x` is positive, then `x ^ 3 ≠ 0`. -/
theorem positiveCube_ne_zero (x : ℝ) (hx : 0 < x) : x ^ 3 ≠ 0 :=
  pow_ne_zero 3 (ne_of_gt hx)
