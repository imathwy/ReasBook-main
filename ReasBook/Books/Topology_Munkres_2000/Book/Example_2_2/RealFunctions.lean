module

public import Mathlib.Data.Real.Basic

public section

/-- The real function `x ↦ 3 * x ^ 2 + 2` used in Examples 2.2 and 2.4. -/
@[expose]
def shiftedQuadratic (x : ℝ) : ℝ := 3 * x ^ 2 + 2

/-- The real function `x ↦ 5 * x` used in Example 2.2. -/
@[expose]
def fiveMul (x : ℝ) : ℝ := 5 * x
