module

import Mathlib.Topology.MetricSpace.Pseudo.Defs

/- Example 18.1. For a function `f : ℝ → ℝ`, topological continuity is equivalent
to the ε–δ condition at every point. -/
#check (Metric.continuous_iff :
  ∀ {f : ℝ → ℝ},
    Continuous f ↔
      ∀ x, ∀ ε > 0, ∃ δ > 0, ∀ y, dist y x < δ → dist (f y) (f x) < ε)
