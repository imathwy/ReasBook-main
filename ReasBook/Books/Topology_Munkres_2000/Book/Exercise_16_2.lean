module

public import Mathlib.Topology.Order

public section

universe u

/-- Exercise 16.2 (1): If `𝒯'` is strictly finer than `𝒯` on `X`, then the topology
that `𝒯'` induces on any subset `Y` is finer than the topology induced by `𝒯`. -/
theorem induced_subtype_mono_of_lt {X : Type u} (Y : Set X)
    {𝒯 𝒯' : TopologicalSpace X} (h_strict : 𝒯' < 𝒯) :
    𝒯'.induced (Subtype.val : Y → X) ≤ 𝒯.induced (Subtype.val : Y → X) :=
  induced_mono h_strict.le

/-- Exercise 16.2 (2): Strictness need not be preserved: on the empty subset, any two
ambient topologies induce the same subspace topology. -/
theorem induced_empty_eq {X : Type u} (𝒯 𝒯' : TopologicalSpace X) :
    𝒯.induced (Subtype.val : (∅ : Set X) → X) =
      𝒯'.induced (Subtype.val : (∅ : Set X) → X) :=
  Subsingleton.elim _ _
