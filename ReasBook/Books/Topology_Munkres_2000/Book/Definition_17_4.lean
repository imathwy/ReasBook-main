module

public import Mathlib.Topology.DerivedSet

public section

/- Definition 17.4: The limit points (cluster points, or points of accumulation)
of a subset `A` of a topological space are the points of `derivedSet A`. -/
#check derivedSet

/-- Membership in the derived set is equivalent to belonging to the closure of
the set after removing the point itself. -/
theorem mem_derivedSet_iff_mem_closure_diff_singleton {X : Type u}
    [TopologicalSpace X] {A : Set X} {x : X} :
    x ∈ derivedSet A ↔ x ∈ closure (A \ {x}) := by
  rw [mem_derivedSet, accPt_principal_iff_clusterPt, mem_closure_iff_clusterPt]
