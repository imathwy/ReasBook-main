module

import Mathlib.Topology.Separation.Regular

public section

universe u

variable {X : Type u}

/- Theorem 32.3. Every compact Hausdorff space is normal.
Here `T4Space` expresses the book's convention that a normal space is also `T₁`. -/
#check fun [TopologicalSpace X] [CompactSpace X] [T2Space X] ↦
  (inferInstance : T4Space X)
