module

import Mathlib.Data.Set.Card

/- Corollary 6.6 (1): If `B` is a subset of the finite set `A`, then `B` is
finite. -/
#check Set.Finite.subset

/- Corollary 6.6 (2): If `B` is a proper subset of the finite set `A`, then
`B.ncard < A.ncard`. -/
#check Set.ncard_lt_ncard
