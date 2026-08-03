module

import Mathlib.Topology.Separation.Hausdorff

universe u

variable (X : Type u) [TopologicalSpace X] [T2Space X] (A : Set X)

/- Exercise 17.12: A subspace of a Hausdorff space is Hausdorff. -/
#check (inferInstance : T2Space A)
