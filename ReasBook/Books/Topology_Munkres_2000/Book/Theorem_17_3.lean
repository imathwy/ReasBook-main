module

import Mathlib.Topology.Constructions

/- Theorem 17.3: If `A` is closed in the subspace `Y` and `Y` is closed in `X`,
then the coercion of `A` to a subset of `X` is closed in `X`. -/
#check IsClosed.trans
