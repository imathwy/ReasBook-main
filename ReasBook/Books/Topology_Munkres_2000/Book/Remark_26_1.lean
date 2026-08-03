module

import Mathlib.Topology.Compactness.Compact

/- Remark 26.1. The modern notion of compactness is `CompactSpace`. By
`isCompact_univ_iff`, this is compactness of the whole space, whose open-cover
formulation is `isCompact_iff_finite_subcover`. It implies the historical property
that every infinite subset has a limit point, expressed by
`Set.Infinite.exists_accPt_principal`.
-/
#check CompactSpace
#check isCompact_univ_iff
#check isCompact_iff_finite_subcover
#check Set.Infinite.exists_accPt_principal
