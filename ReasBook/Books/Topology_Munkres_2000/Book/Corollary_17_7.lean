module

public import Mathlib.Topology.DerivedSet

public section

/- Corollary 17.7. A subset of a topological space is closed if and only if
it contains all its limit points, expressed as `derivedSet A ⊆ A`. -/
#check isClosed_iff_derivedSet_subset
