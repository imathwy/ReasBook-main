module

import Mathlib.Topology.MetricSpace.Basic

universe u

variable (X : Type u) [MetricSpace X]

/- Proposition 21.2: Every metric topology is Hausdorff. For distinct points `x` and `y`,
the disjoint neighborhoods can be taken to be the metric balls of radius `dist x y / 2`,
as a specialization of `Metric.ball_disjoint_ball`. -/
#check (inferInstance : T2Space X)
#check Metric.ball_disjoint_ball
