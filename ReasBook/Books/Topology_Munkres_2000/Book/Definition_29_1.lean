module

public import Topology_Munkres_2000.Book.Definition_29_1.LocalCompactness

/- Definition 29.1 (1): A space `X` is locally compact at `x` when `x` has some
compact neighborhood. -/
#check IsWeaklyLocallyCompactAt

/- Definition 29.1 (2): A space `X` is locally compact when it is locally compact
at every point. -/
#check WeaklyLocallyCompactSpace
