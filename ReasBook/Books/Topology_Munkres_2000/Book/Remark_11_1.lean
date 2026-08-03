module

import Mathlib.Order.Defs.Unbundled

/- Remark 11.1: A strict partial order has the irreflexivity and transitivity
properties of a simple order, represented by `IsStrictOrder`; unlike a simple
order, represented by `IsStrictTotalOrder`, it need not compare every pair of
distinct elements. -/
#check IsStrictOrder
#check IsStrictTotalOrder
