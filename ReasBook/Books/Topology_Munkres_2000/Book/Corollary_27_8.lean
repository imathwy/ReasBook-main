module

public import Mathlib.Analysis.Real.Cardinality

public section

namespace Cardinal.Real

/-- Corollary 27.8: Every closed interval `Set.Icc a b` in `ℝ`, with `a < b`, is
uncountable. This is the nondegenerate case of `Cardinal.Real.Icc_countable_iff`. -/
theorem Icc_not_countable {a b : ℝ} (hab : a < b) : ¬(Set.Icc a b).Countable := by
  rw [Icc_countable_iff]
  exact not_le_of_gt hab

end Cardinal.Real
