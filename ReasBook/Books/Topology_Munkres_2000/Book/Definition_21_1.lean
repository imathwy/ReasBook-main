module

import Mathlib.Topology.Bases

open scoped Topology

universe u

variable (X : Type u) [TopologicalSpace X] (x : X)

/- Definition 21.1. A countable neighborhood basis at `x` is expressed by
`(𝓝 x).IsCountablyGenerated`. Requiring this at every point is the first
countability axiom, `FirstCountableTopology X`. -/
#check (𝓝 x).IsCountablyGenerated
#check FirstCountableTopology X
