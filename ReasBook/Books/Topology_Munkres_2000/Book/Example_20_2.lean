module

import Mathlib.Topology.MetricSpace.Basic

/- Example 20.2: The standard metric on `ℝ` has distance `|x - y|`, induces the
order topology, and identifies open intervals with metric balls. -/
#check Real.metricSpace
#check Real.dist_eq
#check instOrderTopologyReal
#check Real.Ioo_eq_ball
#check Real.ball_eq_Ioo
