import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

-- Proof sketch: rewrite the integer gcd and lcm through their canonical nat-absolute-value
-- descriptions and apply `Nat.gcd_mul_lcm`.
/-- Proposition 1.1.64: for integers `a` and `b`, the product of their greatest common divisor
and least common multiple is the absolute value of `a * b`. -/
theorem gcd_mul_lcm_eq_natAbs_mul (a b : ℤ) :
    Int.gcd a b * Int.lcm a b = Int.natAbs (a * b) := by
  -- Rewrite the integer identity through `natAbs`.
  -- This reduces the goal to the standard natural-number formula.
  simp [Int.gcd_eq_natAbs, Int.lcm_def, Int.natAbs_mul, Nat.gcd_mul_lcm]
