module

public import Mathlib.Topology.Instances.Discrete
public import Mathlib.Topology.Separation.Basic

public section

open Set TopologicalSpace

universe u

namespace DiscreteTopology

/-- Every discrete topological space is locally compact. -/
instance instLocallyCompactSpace {X : Type u} [TopologicalSpace X] [DiscreteTopology X] :
    LocallyCompactSpace X where
  local_compact_nhds x _ hs :=
    ⟨{x}, (isOpen_discrete {x}).mem_nhds rfl, singleton_subset_iff.mpr (mem_of_mem_nhds hs),
      isCompact_singleton⟩

/-- A second-countable discrete topological space has countable underlying type. -/
instance instCountable {X : Type u} [TopologicalSpace X] [DiscreteTopology X]
    [SecondCountableTopology X] : Countable X :=
  TopologicalSpace.separableSpace_iff_countable.mp inferInstance

/-- A second-countable discrete topological space has countable underlying type. -/
theorem countable_of_secondCountable {X : Type u} [TopologicalSpace X] [DiscreteTopology X]
    (h : SecondCountableTopology X) : Countable X := by
  exact TopologicalSpace.separableSpace_iff_countable.mp h.to_separableSpace

end DiscreteTopology

end
