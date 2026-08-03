module

public import Topology_Munkres_2000.Book.Theorem_46_7

public section

open FunctionTopology

/- Exercise 46.2. Prove Theorem 46.7: uniform convergence is finer than compact
convergence, which is finer than pointwise convergence; the first two topologies coincide
for compact domains, and the last two coincide for discrete domains. -/
#check uniform_le_compact
#check compact_le_pointwise
#check uniform_eq_compact_of_compact
#check compact_eq_pointwise_of_discrete
