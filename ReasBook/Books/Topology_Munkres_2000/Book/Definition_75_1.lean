module

import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup
import Mathlib.GroupTheory.Abelianization.Defs

universe u

/- Definition 75.1. For a path-connected space `X`, the group denoted `H₁(X)` is
`Abelianization (FundamentalGroup X x₀)`, equivalently the quotient of
`FundamentalGroup X x₀` by its commutator subgroup. The construction itself only
requires a based space; path connectedness makes its path-induced equivalences between
base points available, and these become independent of the chosen path after
abelianization. -/
#check fun {X : Type u} [TopologicalSpace X] (x₀ : X) ↦
  Abelianization (FundamentalGroup X x₀)
