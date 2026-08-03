module

import Mathlib.Topology.Metrizable.Uniformity

/- Definition 20.4 (1): A topological space is metrizable when its topology is induced
by some metric. -/
#check TopologicalSpace.MetrizableSpace

/- A metrizable topology admits a compatible metric-space structure. -/
#check TopologicalSpace.metrizableSpaceMetric

/- Definition 20.4 (2): A metric space carries a specific metric inducing its topology. -/
#check MetricSpace
