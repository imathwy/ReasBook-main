module

import Topology_Munkres_2000.Book.Definition_15_2
import Mathlib.Topology.Constructions.SumProd

/- Proposition 15.2: For the projections `π₁ : X × Y → X` and `π₂ : X × Y → Y`,
the preimages of `U ⊆ X` and `V ⊆ Y` are `U ×ˢ Set.univ` and
`Set.univ ×ˢ V`; if `U` and `V` are open, these sets are open, and their
intersection is `U ×ˢ V`. -/
#check Set.prod_univ
#check Set.univ_prod
#check IsOpen.prod
#check Set.prod_eq
