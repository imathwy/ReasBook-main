module

import Topology_Munkres_2000.Book.Lemma_2_1

/- Remark 2.3: Lemma 2.1 gives the announced criterion: explicit left and right
inverses make a function bijective, and the two inverse candidates agree. -/
#check Function.Bijective.of_leftInverse_of_rightInverse
#check Function.LeftInverse.eq_rightInverse
