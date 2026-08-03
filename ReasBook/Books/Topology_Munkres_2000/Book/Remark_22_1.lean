module

import Mathlib.Topology.Constructions

/- Remark 22.1: Geometric cut-and-paste constructions, such as forming a torus by
identifying opposite edges of a rectangle or forming a sphere by collapsing the boundary
of a disc to one point, are modeled by a quotient type with its quotient topology. The
canonical projection to this quotient is a quotient map. -/
#check instTopologicalSpaceQuotient
#check isQuotientMap_quotient_mk'
