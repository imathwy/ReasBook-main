module

import Topology_Munkres_2000.Book.Definition_25_4.Neighborhoods

/- Definition 25.4: Local connectedness and local path connectedness at a point are
given by arbitrarily small connected and path-connected neighborhoods, respectively;
the corresponding global properties hold when the pointwise property holds everywhere. -/
#check IsLocallyConnectedAt
#check isLocallyConnectedAt_iff_connected_neighborhoods
#check LocallyConnectedSpace
#check locallyConnectedSpace_iff_isLocallyConnectedAt
#check IsLocallyPathConnectedAt
#check LocallyPathConnectedSpace
#check locallyPathConnectedSpace_iff_isLocallyPathConnectedAt
