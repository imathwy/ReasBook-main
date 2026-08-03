module

import Mathlib.Topology.Connected.Clopen

/- Definition 23.2: A space `X` is connected in the possibly-empty sense of
Definition 23.1 if and only if every clopen subset of `X` is either `∅` or
`Set.univ`. -/
#check preconnectedSpace_iff_clopen
