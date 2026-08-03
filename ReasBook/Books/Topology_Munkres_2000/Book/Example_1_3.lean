module

public import Topology_Munkres_2000.Book.Example_1_1

public section

/- Example 1.3 (1): If a real number `x` is positive, then `x ^ 3 ≠ 0`. -/
#check positiveCube_ne_zero

/-- Example 1.3 (2): If `x ^ 3 = 0`, then it is not true that the real number
`x` is positive. -/
theorem notPosOfCubeEqZero (x : ℝ) (h_cube : x ^ 3 = 0) : ¬ 0 < x :=
  fun hx ↦ positiveCube_ne_zero x hx h_cube
