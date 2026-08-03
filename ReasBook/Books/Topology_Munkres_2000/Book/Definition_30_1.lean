module

import Mathlib.Topology.Bases

open scoped Topology

universe u

variable (X : Type u) [TopologicalSpace X] (x : X)

/- Definition 30.1. A countable neighborhood basis at `x` is represented
canonically by the countable generation of `𝓝 x`. Requiring this at every
point is the first countability axiom. -/
#check (𝓝 x).IsCountablyGenerated
#check FirstCountableTopology X
