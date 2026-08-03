module

import Topology_Munkres_2000.Book.Exercise_37_2.CountableIntersection

/- Definition 37.3. A collection `𝒜` of subsets of `X` has the countable intersection
property if every countable subcollection has nonempty intersection. -/
#check Set.CountableIntersectionProperty
#check Set.CountableIntersectionProperty.iInter_nonempty
