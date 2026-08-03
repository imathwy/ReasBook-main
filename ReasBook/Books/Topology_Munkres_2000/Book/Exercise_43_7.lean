module

public import Mathlib.Analysis.Normed.Lp.lpSpace

public section

open scoped lp

/- Exercise 43.7: the space of square-summable real sequences is complete in the
`ℓ²` metric. -/
#check (inferInstance : CompleteSpace (ℓ²(ℕ, ℝ)))
