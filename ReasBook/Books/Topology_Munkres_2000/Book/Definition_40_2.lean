module

public import Topology_Munkres_2000.Book.Definition_40_2.FSigma

public section

/- Definition 40.2: A subset of a topological space is an `Fσ` set when it is
the union of a countable collection of closed subsets. -/
#check IsFσ

/- The canonical presentation of an `Fσ` set as the union of a sequence of
closed subsets. -/
#check isFσ_iff_eq_iUnion_nat
