module

import Topology_Munkres_2000.Book.Theorem_7_2.Enumeration

/- Remark 9.2. The recursion from Lemma 7.2 selects at each positive index `i`
the least element of `C` not selected at an earlier index. This is exactly the
specification of `C.leastUnused hC` given by `Set.leastUnused_isLeast`. -/
#check Set.leastUnused_isLeast
