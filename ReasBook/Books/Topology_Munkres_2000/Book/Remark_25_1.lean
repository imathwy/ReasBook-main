module

import Topology_Munkres_2000.Book.Definition_25_1.ConnectedComponents

variable {X : Type u} [TopologicalSpace X]

/- Remark 25.1: The relation defining connected components is reflexive, symmetric,
and transitive; transitivity uses the connected union of subsets sharing a point. -/
#check (connectedComponentSetoid X).refl
#check (connectedComponentSetoid X).symm
#check (connectedComponentSetoid X).trans
#check IsConnected.union
