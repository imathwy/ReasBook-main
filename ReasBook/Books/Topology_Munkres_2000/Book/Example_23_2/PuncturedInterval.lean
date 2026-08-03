module

public import Mathlib.Topology.Instances.Real.Lemmas

public section

open scoped Set.Notation

namespace PuncturedInterval

/-- The punctured interval `[-1, 0) ∪ (0, 1]` from Example 23.2. -/
abbrev Space : Set ℝ :=
  Set.Ico (-1 : ℝ) 0 ∪ Set.Ioc 0 1

/-- The negative half `[-1, 0)` of `Space`. -/
abbrev left : Set ℝ :=
  Set.Ico (-1 : ℝ) 0

/-- The positive half `(0, 1]` of `Space`. -/
abbrev right : Set ℝ :=
  Set.Ioc 0 1

/-- The negative half regarded as a subset of `Space`. -/
abbrev leftInSpace : Set Space :=
  Space ↓∩ left

/-- The positive half regarded as a subset of `Space`. -/
abbrev rightInSpace : Set Space :=
  Space ↓∩ right

end PuncturedInterval
