module

public import Mathlib.Topology.Metrizable.Urysohn
public import Mathlib.Topology.Compactness.Lindelof

public section

open TopologicalSpace

universe u

/-- Exercise 34.3. A compact Hausdorff space is metrizable if and only if its topology
has a countable basis. -/
theorem metrizableSpace_iff_secondCountableTopology_of_compact
    {X : Type u} [TopologicalSpace X] [CompactSpace X] [T2Space X] :
    MetrizableSpace X ↔ SecondCountableTopology X := by
  constructor <;> intro <;> infer_instance

end
