module

import Mathlib.Data.Set.Basic

/- Remark 1.3: What meaning does `A ∩ B` have when the sets `A` and `B`
have no elements in common? The intersection is still the set defined by
`Set.inter`; the following definitions identify this set as empty. -/
#check Set.inter
