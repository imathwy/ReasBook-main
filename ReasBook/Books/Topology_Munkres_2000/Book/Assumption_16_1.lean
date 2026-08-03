module

import Topology_Munkres_2000.Book.Example_16_3

/- Assumption 16.1: By convention, every subset of a topological space carries
its canonical subspace topology. -/
#check instTopologicalSpaceSubtype

/- For an order-convex subset of a linearly ordered space with its order
topology, the subspace topology is also the intrinsic order topology. -/
#check orderTopology_of_ordConnected

/- Without order-convexity, the subspace and intrinsic order topologies can
differ. -/
#check LexUnitSquare.topology_ne_induced
