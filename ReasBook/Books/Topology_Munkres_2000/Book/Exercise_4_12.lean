module

import Mathlib.Algebra.Order.Archimedean.Real.Basic

/- Exercise 4.12. The least-upper-bound axiom is needed to prove the
Archimedean ordering property of `ℝ`: the positive integers are unbounded above. -/
#check Real.instArchimedean
#check (exists_nat_gt : ∀ x : ℝ, ∃ n : ℕ, x < n)
