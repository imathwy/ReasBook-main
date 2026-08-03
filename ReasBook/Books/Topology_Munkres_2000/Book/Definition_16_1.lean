module

import Mathlib.Topology.Constructions

/- Definition 16.1: A subset `Y` of a topological space `X` carries the topology
induced by the inclusion `Subtype.val : Y → X`. Its open sets are precisely the
preimages under this inclusion of open subsets of `X`, corresponding to the
intersections `Y ∩ U` in the textbook description. -/
#check instTopologicalSpaceSubtype
#check Topology.IsInducing.subtypeVal
#check Topology.IsInducing.isOpen_iff
#check Topology.IsInducing.image_eq_isOpen_inter_range
