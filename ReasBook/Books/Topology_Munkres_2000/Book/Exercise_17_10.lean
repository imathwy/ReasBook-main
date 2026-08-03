module

import Mathlib.Topology.Order.Basic

public section

universe u

/- Exercise 17.10: Every order topology is Hausdorff. -/
#check fun {X : Type u} [LinearOrder X] [TopologicalSpace X] [OrderTopology X] ↦
  (inferInstance : T2Space X)
