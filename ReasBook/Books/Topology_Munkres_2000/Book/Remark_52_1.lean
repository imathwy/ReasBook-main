module

import Mathlib.Topology.Homotopy.HomotopyGroup

universe u

open scoped Topology

/- Remark 52.1. The types `HomotopyGroup.Pi n X x₀`, written `π_ n X x₀`, are the
homotopy groups of `X` based at `x₀`. Every positive-dimensional homotopy group
has a group structure, and the first homotopy group is multiplicatively equivalent
to `FundamentalGroup X x₀`. -/
#check HomotopyGroup.Pi
#check fun (n : ℕ) (X : Type u) [TopologicalSpace X] (x₀ : X) ↦
  (inferInstance : Group (π_ (n + 1) X x₀))
#check HomotopyGroup.pi1MulEquivFundamentalGroup
