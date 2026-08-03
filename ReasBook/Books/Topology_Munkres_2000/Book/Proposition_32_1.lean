module

import Mathlib.Topology.Order.T5

public section

universe u

/- Proposition 32.1: Every linearly ordered type equipped with its order topology is
normal. Here `T4Space` expresses the book's convention that a normal space is also `T₁`. -/
#check fun (X : Type u) [LinearOrder X] [TopologicalSpace X] [OrderTopology X] ↦
  (inferInstance : T4Space X)
