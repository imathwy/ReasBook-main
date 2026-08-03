module

import Topology_Munkres_2000.Book.Example_20_1.DiscreteMetric

universe u

/- Example 20.1: On any type, the `0`–`1` distance defines a metric whose
induced topology is discrete and whose radius-one ball at `x` is `{x}`. -/
#check DiscreteMetric.space
#check DiscreteMetric.dist_eq
#check DiscreteMetric.dist_eq_zero_of_eq
#check DiscreteMetric.dist_eq_one_of_ne
#check DiscreteMetric.instDiscreteTopology
#check DiscreteMetric.ball_one
