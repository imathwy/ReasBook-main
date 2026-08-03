module

import Mathlib.Topology.Bases

/- Remark 17.5: Although the closed-set definition of `closure` is not convenient
for concrete calculations, closure membership can be characterized using only a
topological basis. -/
#check TopologicalSpace.IsTopologicalBasis.mem_closure_iff
