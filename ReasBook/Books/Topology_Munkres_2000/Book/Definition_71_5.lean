module

import Topology_Munkres_2000.Book.Example_71_1

/- Definition 71.5: The infinite earring is the subspace `InfiniteEarring.Space`
of the Euclidean plane, covered by the countable family `InfiniteEarring.component`
of circles meeting at `InfiniteEarring.origin`. These circles are distinct and
meet pairwise only at the origin, but the space is not their wedge. -/
#check InfiniteEarring.Space
#check InfiniteEarring.component
#check InfiniteEarring.origin
#check InfiniteEarring.component_injective
#check InfiniteEarring.component_inter_component
#check InfiniteEarring.componentHomeomorphicCircle
#check InfiniteEarring.not_isWedgeOfCircles
