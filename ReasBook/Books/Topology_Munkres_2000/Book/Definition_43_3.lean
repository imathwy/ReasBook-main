module

import Mathlib.Topology.MetricSpace.Bounded

universe u v

/- Definition 43.3: A function is bounded when its range is a bounded subset of
the metric codomain. -/
#check fun {X : Type u} {Y : Type v} [MetricSpace Y] (f : X → Y) ↦
  Bornology.IsBounded (Set.range f)

-- The canonical metric characterization by a uniform pairwise distance bound.
#check Metric.isBounded_range_iff
