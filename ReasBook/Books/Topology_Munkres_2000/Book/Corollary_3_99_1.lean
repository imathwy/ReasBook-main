module

import Mathlib.Topology.Algebra.Group.Pointwise

/- Corollary 3.99.1: Let `G` be a topological group and let `A B : Set G`.
If `A` is closed and `B` is compact, then `A * B` is closed. -/
#check IsClosed.mul_right_of_isCompact
