module

import Mathlib.Topology.Closure

/- Definition 48.1: For a subset `A` of a topological space, `interior A` is the
largest open subset contained in `A`; moreover, `interior A = ∅` exactly when
`Aᶜ` is dense. -/
#check interior
#check isOpen_interior
#check interior_subset
#check interior_maximal
#check interior_eq_empty_iff_dense_compl
