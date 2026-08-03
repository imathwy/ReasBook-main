module

public import Mathlib.Topology.MetricSpace.Defs

/- Definition 20.1: A metric on a set `X` is a function `d : X × X → ℝ`
that is nonnegative, vanishes exactly when its arguments are equal, is symmetric,
and satisfies the triangle inequality. -/
#check MetricSpace
#check dist_nonneg
#check dist_eq_zero
#check dist_comm
#check dist_triangle
