module

import Mathlib.Topology.MetricSpace.Defs

universe u

/- Proposition 20.1: A set `U` is open in the metric topology if and only if every
point `y ∈ U` is the center of a ball `Metric.ball y δ ⊆ U` for some `δ > 0`. -/
#check fun {X : Type u} [MetricSpace X] (U : Set X) ↦
  (Metric.isOpen_iff :
    IsOpen U ↔ ∀ y ∈ U, ∃ δ > 0, Metric.ball y δ ⊆ U)
