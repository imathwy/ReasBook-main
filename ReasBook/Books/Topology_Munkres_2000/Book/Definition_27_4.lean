module

import Mathlib.Topology.MetricSpace.Pseudo.Defs

public section

/- Definition 27.4: A map between metric spaces is uniformly continuous. -/
#check UniformContinuous

/- For metric spaces, uniform continuity is characterized by the source's
`ε`-`δ` condition. -/
#check Metric.uniformContinuous_iff
