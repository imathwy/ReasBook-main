module

public import Mathlib.Data.Real.Basic
public import Mathlib.Data.Rel

public section

/-- Example 2.5: The typed function `fun x : ℝ ↦ x ^ 3 + 1` has the same graph
as the rule given by the real ordered pairs satisfying `y = x ^ 3 + 1`. Its
type `ℝ → ℝ` records both the domain and the codomain (called the range by
Munkres here). -/
theorem cubicPlusOneGraph :
    Function.graph (fun x : ℝ ↦ x ^ 3 + 1) =
      {(x, y) : ℝ × ℝ | y = x ^ 3 + 1} := by
  ext ⟨x, y⟩
  exact eq_comm
