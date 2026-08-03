module

import Mathlib.Topology.Separation.Regular

/- Definition 31.2 (1): A regular space in the book's convention is a `T3Space`,
which includes the standing assumption that one-point sets are closed. The underlying
point-versus-closed-set separation property is `RegularSpace`. -/
#check T3Space

/- Definition 31.2 (2): A normal space in the book's convention is a `T4Space`,
which includes the standing assumption that one-point sets are closed. The underlying
closed-set-versus-closed-set separation property is `NormalSpace`. -/
#check T4Space
