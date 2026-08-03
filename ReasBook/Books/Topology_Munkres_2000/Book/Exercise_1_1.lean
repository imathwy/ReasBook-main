module

import Mathlib.Order.BooleanAlgebra.Set

/- Exercise 1.1 (1): Union distributes over intersection. -/
#check Set.union_inter_distrib_left

/- Exercise 1.1 (2): Intersection distributes over union. -/
#check Set.inter_union_distrib_left

/- Exercise 1.1 (3): The complement of a union is the intersection of the
complements. -/
#check Set.compl_union

/- Exercise 1.1 (4): The complement of an intersection is the union of the
complements. -/
#check Set.compl_inter
