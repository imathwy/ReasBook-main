module

public import Mathlib.Topology.Compactness.CountablyCompact

/- Definition 28.4. A topological space `X` is countably compact if every countable
open covering of `X` contains a finite subcollection that covers `X`. -/
#check CountablyCompactSpace
#check isCountablyCompact_univ_iff
#check isCountablyCompact_iff_countable_open_cover
