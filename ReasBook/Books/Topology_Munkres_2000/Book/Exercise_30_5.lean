module

public import Mathlib.Topology.Compactness.Lindelof
public import Mathlib.Topology.Metrizable.Basic

public section

universe u

open TopologicalSpace

/-- Exercise 30.5 (1). Every metrizable space with a countable dense subset
has a countable basis. -/
theorem secondCountableTopology_of_countable_dense {X : Type u}
    [TopologicalSpace X] [MetrizableSpace X] {s : Set X}
    (hs : s.Countable) (hd : Dense s) : SecondCountableTopology X :=
  @UniformSpace.secondCountable_of_separable X (pseudoMetrizableSpaceUniformity X)
    (@pseudoMetrizableSpaceUniformity_countably_generated X _ _) ⟨s, hs, hd⟩

variable (X : Type u) [TopologicalSpace X] [MetrizableSpace X] [LindelofSpace X]

/- Exercise 30.5 (2). Every metrizable Lindelöf space has a countable basis. -/
#check (inferInstance : SecondCountableTopology X)
