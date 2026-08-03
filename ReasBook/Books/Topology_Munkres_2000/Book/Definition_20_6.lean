module

public import Topology_Munkres_2000.Book.Theorem_20_1.BoundedMetric

public section

/- Definition 20.6: `MetricSpace.standardBounded m` is the standard bounded metric
corresponding to a metric `m`; its distance is `min (m.dist x y) 1`. -/
#check MetricSpace.standardBounded
#check MetricSpace.standardBounded_dist
