module

public import Topology_Munkres_2000.Book.Example_1_1

public section

/-- Example 1.2: if a real number has negative square, then it equals `23`;
the implication is vacuously true because a real square is nonnegative. -/
theorem eqTwentyThreeOfSqNeg (x : ℝ) (h_sq_neg : x ^ 2 < 0) : x = 23 :=
  (not_lt_of_ge (sq_nonneg x) h_sq_neg).elim
