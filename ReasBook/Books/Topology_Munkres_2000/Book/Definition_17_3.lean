module

import Mathlib.Topology.Constructions

universe u

/- Definition 17.3: If `Y` is a subspace of a topological space `X`, a set
`A : Set Y` is closed in `Y` when `IsClosed A` holds for the canonical subtype
topology on `Y`; equivalently, `Aᶜ` is open in `Y`. -/
#check fun {X : Type u} [TopologicalSpace X] (Y : Set X) (A : Set Y) ↦ IsClosed A
#check fun {X : Type u} [TopologicalSpace X] (Y : Set X) (A : Set Y) ↦
  (isOpen_compl_iff : IsOpen Aᶜ ↔ IsClosed A)
