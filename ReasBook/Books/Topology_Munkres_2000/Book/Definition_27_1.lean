module

import Mathlib.Topology.MetricSpace.HausdorffDistance

/- Definition 27.1. Let `X` be a metric space and let `A : Set X` be nonempty.
For `x : X`, the distance from `x` to `A` is `Metric.infDist x A`, equivalently
the infimum of `dist x a` over `a ∈ A`. -/
#check Metric.infDist
#check Metric.infDist_eq_iInf
#check Metric.isGLB_infDist
