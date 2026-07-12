import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open Filter
open scoped Topology

noncomputable section

/-- The `n`-th summand in the integer square-pole series. -/
def integer_square_pole_series_term (n : ℤ) (z : ℂ) : ℂ :=
  1 / (z - (n : ℂ)) ^ (2 : ℕ)

/-- Example 2 (1): the meromorphic series `∑ n : ℤ, 1 / (z - n)^2` defines a complex-valued
function by summing over all integers. -/
noncomputable def integer_square_pole_series (z : ℂ) : ℂ :=
  ∑' n : ℤ, integer_square_pole_series_term n z
