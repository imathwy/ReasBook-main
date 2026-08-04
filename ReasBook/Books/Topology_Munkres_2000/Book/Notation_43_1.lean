module

import Topology_Munkres_2000.Book.Definition_20_9

public section

/- Notation 43.1: The cartesian power `Y^J` is written as the function type `J → Y`.
For a metric `m` on `Y`, `MetricSpace.uniformFun m J` equips this function type with the
uniform metric, and `MetricSpace.uniformFun_dist` states
`(m.uniformFun J).dist f g = ⨆ α, min (m.dist (f α) (g α)) 1`. -/
#check MetricSpace.uniformFun
#check MetricSpace.uniformFun_dist
