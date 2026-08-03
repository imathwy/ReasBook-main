module

import Mathlib.Topology.MetricSpace.Basic
import Topology_Munkres_2000.Book.Theorem_20_5.WeightedMetric

/- Exercise 21.3 (1). For a finite family of metric spaces, the product metric
has distance equal to the finite maximum of the coordinate distances. -/
#check metricSpacePi
#check dist_pi_def

/- Exercise 21.3 (2). For a countable family of metric spaces, coordinate
`n : ℕ` represents the textbook index `i = n + 1`; `weightedSupMetricSpace`
uses the truncated coordinate distance divided by `n + 1`. -/
#check Pi.weightedSupMetricSpace
#check Pi.weightedSupMetricSpace_dist
#check Pi.weightedSupMetricSpace_topology
