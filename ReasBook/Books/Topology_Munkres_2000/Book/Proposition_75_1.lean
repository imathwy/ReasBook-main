module

import Topology_Munkres_2000.Book.Definition_52_5.Convention

/- Proposition 75.1. If `X` is path connected and `α : Path x₀ x₁`, then `α`
determines an isomorphism `π₁(X, x₀) ≃* π₁(X, x₁)`. The isomorphism depends on
the chosen path `α`; once `α` is given, path connectedness is not needed by the construction. -/
#check FundamentalGroup.LeftToRight.mulEquivOfPath
