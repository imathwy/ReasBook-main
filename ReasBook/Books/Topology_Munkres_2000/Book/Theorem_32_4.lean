module

import Mathlib.Topology.Order.T5

public section

universe u

/- Theorem 32.4. Every well-ordered set is normal in the order topology.
Here `T4Space` expresses the book's convention that a normal space is also `T₁`. -/
#check fun {X : Type u} [LinearOrder X] [TopologicalSpace X] [OrderTopology X] ↦
  (inferInstance : T4Space X)
