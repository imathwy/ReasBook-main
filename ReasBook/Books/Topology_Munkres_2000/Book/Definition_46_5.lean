module

public import Mathlib.Topology.CompactOpen

public section

/- Definition 46.5: For topological spaces `X` and `Y`, the sets of continuous maps
that send a compact set `K ⊆ X` into an open set `U ⊆ Y` form a subbasis for the
compact-open topology on `C(X, Y)`. -/
#check ContinuousMap.compactOpen
#check ContinuousMap.compactOpen_eq
#check ContinuousMap.isOpen_setOf_mapsTo
