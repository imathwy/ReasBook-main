module

public import Topology_Munkres_2000.Book.Definition_52_5.Convention
public import Topology_Munkres_2000.Book.Notation_52_3.InducedMap

@[expose] public section

universe u

/- Definition 52.5. For a topological space `X` with basepoint `x₀`, the group
`π₁(X, x₀)` is the set of fixed-endpoint path-homotopy classes of loops based at
`x₀`, with Munkres's left-to-right path product. It is the multiplicative opposite
of mathlib's composition-ordered `FundamentalGroup X x₀`. -/
#check FundamentalGroup.LeftToRight
#check FundamentalGroup.LeftToRight.mul_def

variable (X : Type u) [TopologicalSpace X] (x₀ : X)

#check π₁(X, x₀)
#synth Group π₁(X, x₀)
#check FundamentalGroup.LeftToRight.toPath
#check FundamentalGroup.LeftToRight.fromPath
#check FundamentalGroup.LeftToRight.map
#check FundamentalGroup.LeftToRight.mapOfEq
#check FundamentalGroup.LeftToRight.mulEquivOfPath
