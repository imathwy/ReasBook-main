module

public import Mathlib.Topology.Instances.Real.Lemmas

public section

/-- Exercise 18.1. For `f : ℝ → ℝ`, the ε–δ definition of continuity implies
the open set definition. -/
theorem continuous_of_epsilonDelta {f : ℝ → ℝ}
    (h : ∀ x, ∀ ε > 0, ∃ δ > 0, ∀ y, |y - x| < δ → |f y - f x| < ε) :
    Continuous f :=
  Metric.continuous_iff.mpr (by simpa only [Real.dist_eq] using h)
