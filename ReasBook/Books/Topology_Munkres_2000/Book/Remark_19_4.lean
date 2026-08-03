module

import Topology_Munkres_2000.Book.Definition_19_1.BoxTopology

/- Remark 19.4 (1): The whole dependent product is an element of the box basis. -/
#check Pi.univ_mem_boxBasis

/- Remark 19.4 (2): The intersection of two box-basis elements is again a
box-basis element, represented by the coordinatewise intersections. -/
#check Pi.inter_mem_boxBasis
#check Set.pi_inter_distrib
