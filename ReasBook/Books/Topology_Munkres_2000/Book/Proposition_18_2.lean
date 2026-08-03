module

public import Mathlib.Topology.Order

public section

open scoped Topology

universe u v

/-- Proposition 18.2: If `S` generates the topology on `Y`, then a map into `Y` is
continuous whenever the preimage of each member of `S` is open. -/
theorem continuous_of_isOpen_preimage_subbasis {X : Type u} {Y : Type v}
    [TopologicalSpace X] [TopologicalSpace Y] {S : Set (Set Y)} (f : X → Y)
    (hS : (inferInstance : TopologicalSpace Y) = TopologicalSpace.generateFrom S)
    (hf : ∀ U ∈ S, IsOpen (f ⁻¹' U)) : Continuous f := by
  change Continuous[(inferInstance : TopologicalSpace X),
    (inferInstance : TopologicalSpace Y)] f
  rw [hS, continuous_generateFrom_iff]
  exact hf
