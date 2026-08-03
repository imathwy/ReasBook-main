module

import Mathlib.Topology.MetricSpace.Equicontinuity

/- Remark 45.1: For one function, the neighborhood in the metric
characterization of continuity at `x₀` may depend on that function. A family is
equicontinuous at `x₀` exactly when, for every `ε > 0`, one neighborhood of
`x₀` works simultaneously for every function in the family. -/
#check Metric.continuousAt_iff'
#check Metric.equicontinuousAt_iff_right
