module

public import Topology_Munkres_2000.Book.Definition_26_7.PerfectMap
public import Mathlib.Topology.Metrizable.Basic
import Topology_Munkres_2000.Book.Exercise_31_7
import Mathlib.Topology.Metrizable.Urysohn

public section

universe u v

namespace IsPerfectMap

/-- A perfect image of a regular second-countable space is metrizable. -/
theorem metrizableSpace {X : Type u} {Y : Type v}
    [TopologicalSpace X] [TopologicalSpace Y] [T3Space X] [SecondCountableTopology X]
    {p : X → Y} (hp : IsPerfectMap p) : TopologicalSpace.MetrizableSpace Y := by
  -- Local instance justification (proof-local temporary data): Urysohn needs `hp.t3Space`.
  haveI := hp.t3Space
  -- Local instance justification (proof-local temporary data): use `hp.secondCountableTopology`.
  haveI := hp.secondCountableTopology
  infer_instance

end IsPerfectMap
