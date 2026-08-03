module

import Mathlib.Topology.Sets.Closeds

/- Remark 17.2: The closed subsets of a topological space `X` form
`TopologicalSpace.Closeds X`. Taking complements identifies them order-dually
with the open subsets of `X`, explaining their analogous closure properties. -/
#check TopologicalSpace.Closeds
#check TopologicalSpace.Closeds.complOrderIso
