module

import Mathlib.Data.Set.Lattice

/- Definition 1.13: For subsets of a fixed ambient type, mathlib adopts the
convention that the intersection of the empty collection is the whole universe,
even though the book leaves this intersection undefined. -/
#check Set.sInter_empty
