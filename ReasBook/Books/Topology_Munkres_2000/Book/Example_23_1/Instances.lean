module

public import Mathlib.Topology.Connected.Basic
import Mathlib.Topology.Irreducible

public section

namespace IndiscreteTopology

/-- Every nonempty indiscrete topological space is connected. -/
instance connectedSpace (X : Type*) [TopologicalSpace X] [Nonempty X]
    [IndiscreteTopology X] : ConnectedSpace X where
  toPreconnectedSpace := inferInstance
  toNonempty := inferInstance

end IndiscreteTopology
