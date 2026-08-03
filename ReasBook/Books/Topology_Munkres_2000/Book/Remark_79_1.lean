module

import Topology_Munkres_2000.Book.Theorem_79_2

/- Remark 79.1. Theorem 79.2 characterizes equivalences over `B` carrying a chosen
point `e₀` to a specified point `e₀'`. This is finer than unpointed equivalence:
an equivalence may instead carry `e₀` to another point in the fiber of `p'` over `b₀`. -/
#check IsCoveringMap.existsUnique_equiv_iff_fundamentalGroupMapRange_eq
#check CoveringMap.Equivalent
