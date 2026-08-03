module

import Mathlib.Topology.Algebra.Ring.Real
import Mathlib.Topology.Order.Basic

/- Example 16.1: For the closed unit interval `Set.Icc (0 : ℝ) 1`, the
subspace topology inherited from `ℝ` agrees with its intrinsic order topology. -/
#check (inferInstance : OrderTopology (Set.Icc (0 : ℝ) 1))
