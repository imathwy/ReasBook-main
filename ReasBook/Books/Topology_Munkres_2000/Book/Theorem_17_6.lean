module

public import Mathlib.Topology.DerivedSet

public section

/- Theorem 17.6: For a subset `A` of a topological space, its closure is the
union of `A` with its set of limit points `derivedSet A`. -/
#check closure_eq_self_union_derivedSet
