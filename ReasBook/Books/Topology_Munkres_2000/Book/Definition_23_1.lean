module

import Topology_Munkres_2000.Book.Definition_23_1.Separation

/- Definition 23.1 (1): A separation of `X` is a pair of disjoint nonempty open
subsets whose union is `X`. -/
#check Set.IsSeparation

/- Definition 23.1 (2): A space is connected when it admits no separation. -/
#check preconnectedSpace_iff_no_separation
