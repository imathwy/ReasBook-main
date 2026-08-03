module

public import Topology_Munkres_2000.Book.Notation_15_1.Projections

import Mathlib.Data.Prod.Basic

/- Notation 15.1: The projection maps `π₁ : X × Y → X` and
`π₂ : X × Y → Y` are `Prod.fst` and `Prod.snd`. The first projection is
surjective when the second factor is nonempty, and the second projection is
surjective when the first factor is nonempty. -/
#check π₁
#check π₂
#check Prod.fst_surjective
#check Prod.snd_surjective
