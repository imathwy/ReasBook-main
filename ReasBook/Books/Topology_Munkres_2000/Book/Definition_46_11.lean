module

public import Topology_Munkres_2000.Book.Definition_46_11.HomotopyPath

public section

/- Definition 46.11. Give `C(X, Y)` the compact-open topology. When `X` is locally compact,
homotopies from `f` to `g` correspond to paths from `f` to `g` in `C(X, Y)`. This slightly
sharpens the source's locally compact Hausdorff assumption. -/
#check ContinuousMap.compactOpen
#check ContinuousMap.homotopyEquivPath
#check ContinuousMap.Homotopy.toPath
#check Path.toHomotopy
