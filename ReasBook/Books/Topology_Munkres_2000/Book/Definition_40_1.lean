module

public import Topology_Munkres_2000.Book.Definition_33_3

public section

/- Definition 40.1: A subset of a topological space is a `Gδ` set when it is the
intersection of a countable collection of open subsets. This is mathlib's
`IsGδ`. -/
#check IsGδ

/- The canonical presentation of a `Gδ` set as the intersection of a sequence
of open subsets. -/
#check isGδ_iff_eq_iInter_nat
