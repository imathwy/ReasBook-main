module

import Topology_Munkres_2000.Book.Definition_52_5.Convention

/- Remark 52.3. In a path-connected space there is a path between any two
basepoints, and each chosen path induces an equivalence of their fundamental groups.
Because this equivalence depends on the chosen path, it is not a canonical
identification of fundamental groups with different basepoints. -/
#check PathConnectedSpace.joined
#check FundamentalGroup.LeftToRight.mulEquivOfPath
