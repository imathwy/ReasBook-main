module

import Mathlib.Topology.Order

/- Definition 22.5: The quotient topology induced on a set `A` by a map
`p : X → A` is `TopologicalSpace.coinduced p`; its open sets are exactly the
sets `U : Set A` whose preimage `p ⁻¹' U` is open in `X`. -/
#check TopologicalSpace.coinduced
#check isOpen_coinduced
