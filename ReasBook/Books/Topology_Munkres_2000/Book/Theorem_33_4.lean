module

public import Topology_Munkres_2000.Book.Exercise_33_4

public section

/- Theorem 33.4: In a normal space, a subset `A` is closed and `Gδ` if and only if
there is a continuous map to `Set.Icc 0 1` that is zero on `A` and strictly positive
outside `A`. Here `T4Space` expresses the book's convention for a normal space. -/
#check ContinuousMap.exists_vanishesPreciselyOn_iff_closed_isGδ
