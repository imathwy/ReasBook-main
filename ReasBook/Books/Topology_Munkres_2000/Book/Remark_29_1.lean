module

public import Topology_Munkres_2000.Book.Definition_29_1.LocalCompactness
public import Mathlib.Topology.Compactness.LocallyCompact

/- Remark 29.1: The §29 condition that each point has some compact neighborhood is
characterized by `weaklyLocallyCompactSpace_iff`. The usual "arbitrarily small
compact neighborhoods" condition is represented by `LocallyCompactSpace`. -/
#check weaklyLocallyCompactSpace_iff
#check LocallyCompactSpace
#check LocallyCompactSpace.local_compact_nhds
