module

import Mathlib.Topology.Separation.Regular

public section

universe u

variable {X : Type u}

/- Theorem 32.1: Every regular space with a countable basis is normal.
Here `T3Space` and `T4Space` express the book's convention that regular and normal
spaces are also `T₁`. -/
#check fun [TopologicalSpace X] [T3Space X] [SecondCountableTopology X] ↦
  (inferInstance : T4Space X)
