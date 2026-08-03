module

import Mathlib.Topology.MetricSpace.HausdorffDistance

public section

/- Proposition 27.1. For a fixed nonempty set `A` in a metric space, the function
`x ↦ Metric.infDist x A` is continuous. In fact, the conclusion holds without the
nonemptiness assumption. -/
#check Metric.continuous_infDist_pt
