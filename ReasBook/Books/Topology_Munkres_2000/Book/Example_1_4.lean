module

public import Topology_Munkres_2000.Book.Example_1_2

public section

/- Example 1.4 (1): If a real number `x` satisfies `x ^ 2 < 0`, then `x = 23`. -/
#check eqTwentyThreeOfSqNeg

/-- Example 1.4 (2): If a real number `x` is not equal to `23`, then it is not
true that `x ^ 2 < 0`. -/
theorem notSqNegOfNeTwentyThree (x : ℝ) (h_ne : x ≠ 23) : ¬ x ^ 2 < 0 :=
  mt (eqTwentyThreeOfSqNeg x) h_ne
