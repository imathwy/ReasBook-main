module

public import Topology_Munkres_2000.Book.Example_1_2

public section

/- Example 1.6 (1): the implication `x ^ 2 < 0 → x = 23` is true for real `x`. -/
#check eqTwentyThreeOfSqNeg

/-- Example 1.6 (2): the converse `x = 23 → x ^ 2 < 0` is not true for every
real `x`. -/
theorem not_sqNegOfEqTwentyThree : ¬ ∀ x : ℝ, x = 23 → x ^ 2 < 0 := by
  intro h
  exact (not_lt_of_ge (sq_nonneg (23 : ℝ))) (h 23 rfl)
