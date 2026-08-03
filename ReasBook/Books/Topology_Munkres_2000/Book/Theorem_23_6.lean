module

import Mathlib.Topology.Connected.Basic

universe u

variable {n : ℕ} {X : Fin n → Type u}
variable [(i : Fin n) → TopologicalSpace (X i)] [∀ i, ConnectedSpace (X i)]

/- Theorem 23.6: A finite Cartesian product of connected spaces is connected.
The finite family is indexed by `Fin n`. -/
#check (inferInstance : ConnectedSpace ((i : Fin n) → X i))

/- Mathlib provides the stronger result for arbitrary Cartesian products. -/
#check instConnectedSpaceForall
