module

import Mathlib.Topology.Homotopy.Path

/- Definition 51.5: Path concatenation induces composition on path-homotopy
classes, with the class of `f.trans g` equal to the composite of the classes. -/
#check Path.Homotopic.Quotient.trans
#check Path.Homotopic.Quotient.mk_trans
