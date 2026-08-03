module

import Mathlib.Topology.Separation.Regular

universe u

/- Exercise 32.3: Every locally compact Hausdorff space is regular.
Here `T3Space` expresses the book's convention for a regular space. -/
#check fun (X : Type u) [TopologicalSpace X] [LocallyCompactSpace X] [T2Space X] ↦
  (inferInstance : T3Space X)
