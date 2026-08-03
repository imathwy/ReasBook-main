module

public import Topology_Munkres_2000.Book.Theorem_3_99_1

public section

/- Exercise 3.99.6: A point belongs to the closure of `A` if and only if some
directed net of points of `A` converges to it. -/
#check mem_closure_iff_exists_tendsto_net
