module

import Mathlib.Topology.Order.Basic

universe u

variable (X : Type u) [LinearOrder X] [TopologicalSpace X] [OrderTopology X]
variable (a b : X)

/- Remark 14.1: Every open interval `Set.Ioo a b` in a simply ordered set
equipped with its order topology is an open set. -/
#check (isOpen_Ioo : IsOpen (Set.Ioo a b))
