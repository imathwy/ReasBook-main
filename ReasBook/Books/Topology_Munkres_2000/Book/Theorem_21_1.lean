module

import Mathlib.Topology.MetricSpace.Defs

universe u v

/- Theorem 21.1. A map between metric spaces is continuous if and only if it
satisfies the pointwise ε–δ condition. -/
#check (Metric.continuous_iff :
  ∀ {X : Type u} {Y : Type v} [MetricSpace X] [MetricSpace Y] {f : X → Y},
    Continuous f ↔
      ∀ x, ∀ ε > 0, ∃ δ > 0, ∀ y, dist y x < δ → dist (f y) (f x) < ε)
