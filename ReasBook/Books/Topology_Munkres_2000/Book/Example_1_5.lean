module

public import Topology_Munkres_2000.Book.Example_1_1

public section

/- Example 1.5 (1): if a real number `x` is positive, then `x ^ 3 ≠ 0`. -/
#check positiveCube_ne_zero

/-- Example 1.5 (2): the converse `x ^ 3 ≠ 0 → 0 < x` is not true for every
real `x`. -/
theorem notPosOfCubeNeZero : ¬ ∀ x : ℝ, x ^ 3 ≠ 0 → 0 < x := by
  intro h
  exact (by norm_num : ¬ (0 : ℝ) < -1) (h (-1) (by norm_num))
