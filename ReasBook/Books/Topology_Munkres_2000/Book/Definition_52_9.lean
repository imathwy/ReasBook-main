module

import Topology_Munkres_2000.Book.Definition_52_5.Convention

/- Definition 52.9: For a continuous map `h : C(X, Y)` carrying `x₀` to `y₀`,
the induced homomorphism `h_* : π₁(X, x₀) →* π₁(Y, y₀)` is
`FundamentalGroup.LeftToRight.mapOfEq h`. It sends each based loop-homotopy class
to the class obtained by postcomposing with `h`. -/
#check FundamentalGroup.LeftToRight.mapOfEq
#check FundamentalGroup.LeftToRight.mapOfEq_apply
