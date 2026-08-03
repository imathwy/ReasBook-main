module

import Mathlib.Data.Set.Basic

/- Remark 1.4: The empty set has no elements, and union or intersection with it
has the conventional behavior stated in the source. -/
#check Set.mem_empty_iff_false
#check Set.union_empty
#check Set.inter_empty
