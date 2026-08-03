module

public import Mathlib.Topology.Order

public section

universe u

variable {X : Type u} [TopologicalSpace X] [DiscreteTopology X]

/- Example 17.4 (1): In the discrete topology on `X`, every set is open. -/
#check (isOpen_discrete : ∀ s : Set X, IsOpen s)

/- Example 17.4 (2): In the discrete topology on `X`, every set is closed. -/
#check (isClosed_discrete : ∀ s : Set X, IsClosed s)
