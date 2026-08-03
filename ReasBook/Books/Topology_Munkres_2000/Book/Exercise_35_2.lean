module

public import Mathlib.Data.Real.Basic

public section

/-- Exercise 35.2: If the Tietze approximation step divides `[-r, r]` at `±a * r`,
the uniform residual factor is `max (1 - a) (2 * a)`. This factor is strictly
contractive exactly when `0 < a < 1 / 2`, so among the source range `0 < a < 1`
the proof works for every such `a`, not only `a = 1 / 3`. -/
theorem tietzeStepErrorFactor_lt_one_iff (a : ℝ) :
    max (1 - a) (2 * a) < 1 ↔ 0 < a ∧ a < 1 / 2 := by
  -- Split the contraction bound into the outer- and middle-interval errors.
  rw [max_lt_iff]
  constructor
  · intro errorBounds
    -- Each error bound gives one endpoint of the admissible range for `a`.
    constructor
    · exact (sub_lt_self_iff 1).mp errorBounds.1
    · apply (lt_div_iff₀ zero_lt_two).mpr
      simpa [mul_comm] using errorBounds.2
  · intro parameterBounds
    -- Conversely, the two parameter inequalities make both errors contractive.
    constructor
    · exact (sub_lt_self_iff 1).mpr parameterBounds.1
    · have middleError : a * 2 < 1 := (lt_div_iff₀ zero_lt_two).mp parameterBounds.2
      simpa [mul_comm] using middleError
