module

import Topology_Munkres_2000.Book.Definition_52_5.Convention

/- Proposition 52.3: Postcomposition by a continuous map preserves
fixed-endpoint path homotopy, so it descends to path-homotopy classes.
It commutes with path concatenation, and therefore the pointed induced map
`FundamentalGroup.LeftToRight.mapOfEq h` is a homomorphism. -/
#check Path.Homotopic.map
#check Path.Homotopic.Quotient.map
#check Path.map_trans
#check FundamentalGroup.LeftToRight.mapOfEq
#check FundamentalGroup.LeftToRight.mapOfEq_apply
