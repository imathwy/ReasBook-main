module

import Mathlib.Order.SetNotation

/- Proposition 1.4 (1): The union operation extends from two sets to an
arbitrary collection of sets. -/
#check Set.sUnion

/- Proposition 1.4 (2): The intersection operation extends from two sets to an
arbitrary collection of sets. Mathlib's `Set.sInter` assigns the universal set
to the empty collection, whereas the book later leaves that case undefined. -/
#check Set.sInter
