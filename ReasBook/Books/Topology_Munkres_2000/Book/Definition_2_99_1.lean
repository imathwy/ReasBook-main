module

import Mathlib.Topology.Algebra.Group.Defs
import Mathlib.Topology.Separation.Basic

universe u

/- Definition 2.99.1: A topological group in the source is represented in mathlib by a type
`G` with `TopologicalSpace G`, `Group G`, `T1Space G`, and `IsTopologicalGroup G`.
The last class extends `ContinuousMul G` and `ContinuousInv G`. -/
#check fun (G : Type u) [TopologicalSpace G] [Group G] [T1Space G]
    [IsTopologicalGroup G] ↦ G
