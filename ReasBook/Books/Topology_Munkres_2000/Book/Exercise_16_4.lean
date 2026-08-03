module

import Mathlib.Topology.Constructions.SumProd

/- Exercise 16.4: A map is open when the image of every open set is open. The
coordinate projections `Prod.fst : X × Y → X` and `Prod.snd : X × Y → Y` are
open maps for the product topology. -/
#check IsOpenMap
#check isOpenMap_fst
#check isOpenMap_snd
