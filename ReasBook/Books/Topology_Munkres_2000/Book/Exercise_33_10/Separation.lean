module

public import Mathlib.Topology.Algebra.IsUniformGroup.Defs
public import Mathlib.Topology.UniformSpace.Uniformizable

universe u

public section

namespace IsTopologicalGroup

/-- A topological group is completely regular via its canonical right uniformity. -/
instance completelyRegularSpace (G : Type u) [TopologicalSpace G] [Group G]
    [IsTopologicalGroup G] : CompletelyRegularSpace G :=
  @UniformSpace.toCompletelyRegularSpace G (rightUniformSpace G)

/-- A T₁ topological group is a T₃.₅ space. -/
instance t35Space (G : Type u) [TopologicalSpace G] [Group G]
    [IsTopologicalGroup G] [T1Space G] : T35Space G where
  toT0Space := inferInstance
  toCompletelyRegularSpace := inferInstance

end IsTopologicalGroup
