module

import Mathlib.Topology.Maps.Basic
import Topology_Munkres_2000.Book.Exercise_22_3

/- Proposition 22.2 (1): A surjective continuous open map is a quotient map. -/
#check IsOpenMap.isQuotientMap

/- Proposition 22.2 (2): A surjective continuous closed map is a quotient map. -/
#check IsClosedMap.isQuotientMap

/- Proposition 22.2 (3): There is a quotient map that is neither open nor closed. -/
#check HalfPlaneAxisProjection.quotient_not_open_not_closed
