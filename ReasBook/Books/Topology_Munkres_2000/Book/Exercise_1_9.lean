module

import Mathlib.Data.Set.Lattice

public section

/- Exercise 1.9 (1): The complement of an arbitrary union is the intersection
of the complements. -/
#check Set.compl_sUnion

/- Exercise 1.9 (2): The complement of an arbitrary intersection is the union
of the complements. -/
#check Set.compl_sInter
