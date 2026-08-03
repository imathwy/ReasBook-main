module

import Mathlib.Topology.Separation.Regular

universe u

/- Exercise 32.4: Every regular Lindelöf space is normal.
Here `T3Space` and `T4Space` express the book's conventions for regular and normal spaces. -/
#check fun (X : Type u) [TopologicalSpace X] [T3Space X] [LindelofSpace X] ↦
  (inferInstance : T4Space X)
