module

import Mathlib.Topology.MetricSpace.Basic

/- Exercise 21.1: If `A` is a subset of a metric space `X`, then the ambient
distance restricted to `A × A` is a metric inducing the subspace topology on `A`. -/
#check Subtype.metricSpace
#check Subtype.dist_eq
#check toTopologicalSpace_subtype
