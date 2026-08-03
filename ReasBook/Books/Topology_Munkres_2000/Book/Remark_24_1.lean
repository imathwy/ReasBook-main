module

import Topology_Munkres_2000.Book.Definition_24_3.PathConnectedness

/- Remark 24.1: If every pair of points of a topological space can be joined by a
path, then the space is connected. -/
#check PathPreconnectedSpace.toPreconnectedSpace

/- The source hypothesis is exactly `PathPreconnectedSpace`. -/
#check pathPreconnectedSpace_iff
