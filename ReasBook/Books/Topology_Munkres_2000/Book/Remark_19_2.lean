module

import Mathlib.Topology.Bases

/- Remark 19.2: The product topology has a basis of finite-coordinate cylinders
`(F : Set ι).pi U`. Such a cylinder is the finite intersection of the inverse
images of the sets `U i` under the coordinate projections for `i ∈ F`. A point
belongs to it exactly when its `i`th coordinate belongs to `U i` for `i ∈ F`;
coordinates outside `F` are unrestricted. -/
#check isTopologicalBasis_pi
#check Set.pi_def
#check Set.mem_pi
