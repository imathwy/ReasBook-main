module

import Mathlib.Topology.Defs.Filter

/- Definition 18.2: Condition (4) says that a function `f : X → Y` between
topological spaces is continuous at `x : X` if every neighborhood `V` of `f x`
contains `f '' U` for some neighborhood `U` of `x`. -/
#check ContinuousAt
