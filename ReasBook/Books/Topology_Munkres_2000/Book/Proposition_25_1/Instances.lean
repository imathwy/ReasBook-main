module

public import Mathlib.Topology.Connected.Clopen
public import Mathlib.Topology.Separation.Basic

public section

namespace ConnectedComponents

/-- The quotient topology on the connected components of a space is `T1`. -/
instance instT1Space {X : Type u} [TopologicalSpace X] :
    T1Space (ConnectedComponents X) where
  t1 C := by
    obtain ⟨x, rfl⟩ := surjective_coe C
    rw [← isQuotientMap_coe.isClosed_preimage, connectedComponents_preimage_singleton]
    exact isClosed_connectedComponent

end ConnectedComponents
