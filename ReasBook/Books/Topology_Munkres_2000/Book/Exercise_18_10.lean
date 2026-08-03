module

import Mathlib.Topology.Constructions.SumProd

/- Exercise 18.10: For continuous maps `f : A → B` and `g : C → D`, the
coordinatewise product map denoted in the source by `f × g` is `Prod.map f g`,
which sends `(a, c)` to `(f a, g c)`, and is continuous. -/
#check Continuous.prodMap
