module

import Mathlib.Topology.Neighborhoods

universe u v

/- Definition 3.99.3: A net `net : J → X` converges to `x : X` when
`Filter.Tendsto net Filter.atTop (nhds x)` holds. -/
#check fun {J : Type u} {X : Type v} [Nonempty J] [PartialOrder J]
    [IsDirectedOrder J] [TopologicalSpace X] (net : J → X) (x : X) ↦
  Filter.Tendsto net Filter.atTop (nhds x)

/- Equivalently, every neighborhood `U` of `x` contains `net β` for all `β`
beyond some index `α`. -/
#check fun {J : Type u} {X : Type v} [Nonempty J] [PartialOrder J]
    [IsDirectedOrder J] [TopologicalSpace X] (net : J → X) (x : X) ↦
  (Filter.tendsto_atTop' :
    Filter.Tendsto net Filter.atTop (nhds x) ↔
      ∀ U ∈ nhds x, ∃ α, ∀ β, α ≤ β → net β ∈ U)
