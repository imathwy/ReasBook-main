module

import Topology_Munkres_2000.Book.Definition_15_1

/- Theorem 15.1: If `𝓑` and `𝓒` are topological bases on `X` and `Y`,
respectively, then the products `B ×ˢ C` form a topological basis on `X × Y`.
The collection of these products is represented by `Set.image2`. -/
#check TopologicalSpace.IsTopologicalBasis.prod
