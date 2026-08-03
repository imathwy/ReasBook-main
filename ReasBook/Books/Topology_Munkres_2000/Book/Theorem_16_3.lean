module

import Mathlib.Topology.Constructions.SumProd

universe u v

/- Theorem 16.3: For subspaces `A ⊆ X` and `B ⊆ Y`, the product topology on
`A × B` is the topology induced from `X × Y` by the coordinatewise inclusion. -/
#check fun {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    (A : Set X) (B : Set Y) ↦
  prod_induced_induced (fun a : A ↦ a) (fun b : B ↦ b)
