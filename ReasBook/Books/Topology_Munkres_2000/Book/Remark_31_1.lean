module

import Mathlib.Topology.Separation.Regular
import Topology_Munkres_2000.Book.Definition_23_1.Separation

/- Remark 31.1: The separation axioms `T2Space`, `T3Space`, and `T4Space`
separate specified points or closed sets by disjoint open neighborhoods. In the
connectedness setting, `Set.IsSeparation U V` instead means that `U` and `V` are
disjoint nonempty open sets whose union is the entire space. -/
#check T2Space
#check T3Space
#check T4Space
#check Set.IsSeparation
#check preconnectedSpace_iff_no_separation
