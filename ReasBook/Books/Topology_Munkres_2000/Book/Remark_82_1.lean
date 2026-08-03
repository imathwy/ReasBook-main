module

public import Topology_Munkres_2000.Book.Remark_82_1.Classification

import Topology_Munkres_2000.Book.Proposition_81_2

public section

/- Remark 82.1. For a based space `B`, the injective classification map from equivalence classes
of connected coverings of `B` to conjugacy classes of subgroups of `π₁(B, b₀)` raises the question
of whether it is surjective. -/
#check ConnectedCovering.IsClassificationSurjective
