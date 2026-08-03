module

import Mathlib.Topology.Order.Basic

universe u

variable (X : Type u) [LinearOrder X] [TopologicalSpace X] [OrderTopology X]
variable (a : X)

/- Proposition 14.1 (1): In a simply ordered set equipped with its order topology,
the open ray `Set.Ioi a` is open. -/
#check (isOpen_Ioi' a : IsOpen (Set.Ioi a))

/- Proposition 14.1 (2): In a simply ordered set equipped with its order topology,
the open ray `Set.Iio a` is open. -/
#check (isOpen_Iio' a : IsOpen (Set.Iio a))
