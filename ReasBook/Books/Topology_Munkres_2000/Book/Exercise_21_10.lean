module

public import Mathlib.Topology.Algebra.Ring.Real

public section

/-- Exercise 21.10 (1): The hyperbola defined by `x * y = 1` is closed in `ℝ × ℝ`. -/
theorem hyperbolaIsClosed : IsClosed {p : ℝ × ℝ | p.1 * p.2 = 1} :=
  isClosed_eq (continuous_fst.mul continuous_snd) continuous_const

/-- Exercise 21.10 (2): The unit circle defined by `x ^ 2 + y ^ 2 = 1` is closed in
`ℝ × ℝ`. -/
theorem unitCircleIsClosed : IsClosed {p : ℝ × ℝ | p.1 ^ 2 + p.2 ^ 2 = 1} :=
  isClosed_eq ((continuous_fst.pow 2).add (continuous_snd.pow 2)) continuous_const

/-- Exercise 21.10 (3): The closed unit disk defined by `x ^ 2 + y ^ 2 ≤ 1` is closed
in `ℝ × ℝ`. -/
theorem closedUnitDiskIsClosed :
    IsClosed {p : ℝ × ℝ | p.1 ^ 2 + p.2 ^ 2 ≤ 1} :=
  isClosed_le ((continuous_fst.pow 2).add (continuous_snd.pow 2)) continuous_const

end
