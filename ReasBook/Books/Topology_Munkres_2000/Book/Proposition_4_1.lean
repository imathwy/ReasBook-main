module

import Mathlib.Data.Real.Basic

/- Proposition 4.1 (1): If `x > y` and `z < 0` in `ℝ`, then
`x * z < y * z`. -/
#check (mul_lt_mul_of_neg_right :
  ∀ {x y z : ℝ}, y < x → z < 0 → x * z < y * z)

/- Proposition 4.1 (2): In `ℝ`, one has `-1 < 0`. -/
#check (neg_one_lt_zero : (-1 : ℝ) < 0)

/- Proposition 4.1 (3): In `ℝ`, one has `0 < 1`. -/
#check Real.zero_lt_one
