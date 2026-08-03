module

import Mathlib.Topology.Closure

/- Remark 17.4: Mathlib writes the interior and closure of `A` as `interior A`
and `closure A`. The interior is open, the closure is closed,
`interior A ⊆ A ⊆ closure A`, and open or closed sets are fixed by the
corresponding operation. -/
#check interior
#check closure
#check isOpen_interior
#check isClosed_closure
#check interior_subset
#check subset_closure
#check IsOpen.interior_eq
#check IsClosed.closure_eq
