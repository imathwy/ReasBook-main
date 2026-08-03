module

public import Mathlib.Analysis.Seminorm

public section

/-- Exercise 1.3 (1): The original statement in part (a) is true: if `x < 0`,
then `0 < x ^ 2 - x`. -/
theorem sqSubSelfPosOfNeg (x : ℝ) (hx : x < 0) : 0 < x ^ 2 - x := by
  -- The square is nonnegative, while subtracting a negative number is positive.
  nlinarith [sq_nonneg x]

/-- Exercise 1.3 (2): The contrapositive in part (a) is true: if
`x ^ 2 - x ≤ 0`, then `0 ≤ x`. -/
theorem nonnegOfSqSubSelfNonpos (x : ℝ) (hx : x ^ 2 - x ≤ 0) : 0 ≤ x := by
  -- A negative input would make the quadratic expression strictly positive.
  nlinarith [sq_nonneg x]

/-- Exercise 1.3 (3): The converse in part (a), that
`0 < x ^ 2 - x → x < 0` for every real `x`, is false. -/
theorem notForallNegOfSqSubSelfPos : ¬ ∀ x : ℝ, 0 < x ^ 2 - x → x < 0 := by
  -- At `x = 2`, the quadratic expression is positive but the input is not negative.
  intro h
  have hTwo := h 2
  norm_num at hTwo

/-- Exercise 1.3 (4): The original statement in part (b), that
`0 < x → 0 < x ^ 2 - x` for every real `x`, is false. -/
theorem notForallSqSubSelfPosOfPos : ¬ ∀ x : ℝ, 0 < x → 0 < x ^ 2 - x := by
  -- At `x = 1 / 2`, the input is positive but the quadratic expression is negative.
  intro h
  have hHalf := h (1 / 2)
  norm_num at hHalf

/-- Exercise 1.3 (5): The contrapositive in part (b), that
`x ^ 2 - x ≤ 0 → x ≤ 0` for every real `x`, is false. -/
theorem notForallNonposOfSqSubSelfNonpos :
    ¬ ∀ x : ℝ, x ^ 2 - x ≤ 0 → x ≤ 0 := by
  -- The same midpoint has a nonpositive quadratic value while remaining positive.
  intro h
  have hHalf := h (1 / 2)
  norm_num at hHalf

/-- Exercise 1.3 (6): The converse in part (b), that
`0 < x ^ 2 - x → 0 < x` for every real `x`, is false. -/
theorem notForallPosOfSqSubSelfPos : ¬ ∀ x : ℝ, 0 < x ^ 2 - x → 0 < x := by
  -- At `x = -1`, the quadratic expression is positive but the input is negative.
  intro h
  have hNegOne := h (-1)
  norm_num at hNegOne
