module

import Mathlib.Topology.Order

/- Exercise 16.1: For `A : Set Y` and `Y : Set X`, take `f` and `g` in
`induced_compose` to be the subtype inclusions `A → Y` and `Y → X`. The
composite is the direct inclusion `A → X`, so the two induced topologies agree. -/
#check induced_compose
