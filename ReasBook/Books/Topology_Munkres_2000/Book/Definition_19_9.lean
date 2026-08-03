module

import Topology_Munkres_2000.Book.Definition_19_9.ProductTopology

/- Definition 19.9: For each coordinate `i`, `Pi.projectionSubbasis X i` consists
of inverse images of open sets under `Function.eval i`; their union is
`Pi.productSubbasis X`, and the topology it generates is the product topology. -/
#check Pi.projectionSubbasis
#check Pi.productSubbasis
#check Pi.topologicalSpace_eq_generateFrom
