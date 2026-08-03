module

public import Topology_Munkres_2000.Book.Definition_16_4

/- Definition 24.2: A subset of a linear order is convex when it contains the
interval between each pair of its points; this is `Set.OrdConnected`. -/
#check Set.OrdConnected

-- The earlier source-facing companion gives the equivalent strict-interval formulation.
#check Set.ordConnected_iff_Ioo
