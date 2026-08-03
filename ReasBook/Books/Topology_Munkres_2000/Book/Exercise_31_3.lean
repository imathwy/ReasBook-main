module

import Mathlib.Topology.Order.T5

public section

universe u

/- Exercise 31.3: Every order topology is regular. -/
#check fun {X : Type u} [LinearOrder X] [TopologicalSpace X] [OrderTopology X] ↦
  (inferInstance : T3Space X)
