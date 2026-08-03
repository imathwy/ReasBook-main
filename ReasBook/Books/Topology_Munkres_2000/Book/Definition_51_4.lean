module

import Mathlib.Topology.Path

/- Definition 51.4: The textbook product `f * g`, which traverses `f` on the
first half of `unitInterval` and `g` on the second half, is `f.trans g`.
The theorem `Path.trans_apply` gives the two piecewise evaluation equations. -/
#check Path.trans
#check Path.trans_apply
