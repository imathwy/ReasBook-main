module

public import Topology_Munkres_2000.Book.Definition_40_2.FSigma

public section

/- Exercise 40.2: A subset `W` of a topological space `X` is an `Fσ` set if and only
if its complement `Wᶜ` is a `Gδ` set. -/
#check isFσ_iff_compl_isGδ
