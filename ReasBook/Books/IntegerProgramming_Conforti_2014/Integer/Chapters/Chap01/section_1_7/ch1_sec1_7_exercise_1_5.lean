import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

-- Semantic search tool `lean_leansearch` was not available in this environment; this item uses
-- a direct stopping-rule predicate and a companion approximation guarantee.

/-- Exercise 1.5. A `p%`-approximate Step 4 for branch-and-bound may stop once the incumbent
objective value `zBar` is at least `(1 - p / 100)` times the current global upper bound on the
optimal value. -/
def branch_and_bound_relative_gap_step (p zBar upperBound : ℝ) : Prop :=
  (1 - p / 100) * upperBound ≤ zBar

/-- If the current branch-and-bound upper bound dominates the positive optimum value, then the
relative-gap stopping rule certifies that the incumbent value is within `p%` of optimal. -/
theorem branch_and_bound_relative_gap_step_spec
    {p zBar zStar upperBound : ℝ}
    (hp_nonneg : 0 ≤ p)
    (hp_le_hundred : p ≤ 100)
    (hzStar_pos : 0 < zStar)
    (hupper : zStar ≤ upperBound)
    (hstep : branch_and_bound_relative_gap_step p zBar upperBound) :
    zBar / zStar ≥ 1 - p / 100 := sorry
