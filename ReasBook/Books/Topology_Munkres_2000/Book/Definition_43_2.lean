module

import Topology_Munkres_2000.Book.Definition_20_9.UniformMetric

/- Definition 43.2: For a metric `m` on `Y`, `MetricSpace.uniformFun m J` is the
uniform metric on the cartesian power `J → Y`. Its distance is the supremum of the
coordinatewise standard bounded distances `min (m.dist (f j) (g j)) 1`. -/
#check MetricSpace.uniformFun
#check MetricSpace.uniformFun_dist
#check MetricSpace.uniformFun_dist_le_one
