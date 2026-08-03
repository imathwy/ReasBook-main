module

import Mathlib.Order.Directed

/- Definition 3.99.2: A directed set is represented by a type `J` with
`[PartialOrder J] [IsDirectedOrder J]`; the latter class states that every pair
of elements has a common upper bound. -/
#check IsDirectedOrder

#check exists_ge_ge
