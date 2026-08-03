module

import Mathlib.Topology.Algebra.Group.Pointwise

universe u

open scoped Pointwise

/- Exercise 3.99.11: Let `G` be a topological group and let `A B : Set G`.
If `A` is closed and `B` is compact, then `A * B` is closed. -/
#check fun {G : Type u} [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
    {A B : Set G} (hA : IsClosed A) (hB : IsCompact B) ↦
  IsClosed.mul_right_of_isCompact hA hB
