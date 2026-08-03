module

import Mathlib.Topology.Connected.Basic

universe u v

variable {ι : Type u} {X : ι → Type v}
variable [(i : ι) → TopologicalSpace (X i)] [∀ i, ConnectedSpace (X i)]

/- Theorem 23.1: An arbitrary product of connected spaces is connected in the
product topology. -/
#check (inferInstance : ConnectedSpace ((i : ι) → X i))
