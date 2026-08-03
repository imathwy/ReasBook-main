module

public import Topology_Munkres_2000.Book.Definition_24_3.PathConnectedness

/- Definition 24.3: `Path x y` is the canonical path on the unit interval from `x`
to `y`, and `Joined x y` asserts that such a path exists. -/
#check Path
#check Joined

/- Definition 24.3: A space is path connected when every pair of points can be joined by a path.
The empty-allowed source condition is represented by `PathPreconnectedSpace`. -/
#check PathPreconnectedSpace
#check pathPreconnectedSpace_iff
