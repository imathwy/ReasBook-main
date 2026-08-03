module

import Mathlib.Topology.Order.Basic

public section

universe u v

section OrderTopology

variable (α : Type u) [LinearOrder α] [TopologicalSpace α] [OrderTopology α]

/- Theorem 17.11 (1): Every simply ordered set is Hausdorff in its order topology. -/
#check (inferInstance : T2Space α)

end OrderTopology

section Product

variable (X : Type u) (Y : Type v)
variable [TopologicalSpace X] [T2Space X] [TopologicalSpace Y] [T2Space Y]

/- Theorem 17.11 (2): The product of two Hausdorff spaces is Hausdorff. -/
#check (inferInstance : T2Space (X × Y))

end Product

section Subspace

variable (X : Type u) [TopologicalSpace X] [T2Space X] (A : Set X)

/- Theorem 17.11 (3): A subspace of a Hausdorff space is Hausdorff. -/
#check (inferInstance : T2Space A)

end Subspace
