module

import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup

public section

/- Definition 52.1. For a topological space `X` with chosen basepoint `x₀`,
`FundamentalGroup X x₀` is the group of path-homotopy classes of loops based at `x₀`.
Mathlib's multiplication traverses the right factor first; the source's left-to-right
convention is introduced with the notation `π₁(X, x₀)` in Definition 52.4. -/
#check FundamentalGroup

universe u

variable (X : Type u) [TopologicalSpace X] (x₀ : X)

#synth Group (FundamentalGroup X x₀)
#check FundamentalGroup.toPath
#check FundamentalGroup.fromPath
