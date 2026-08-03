module

import Topology_Munkres_2000.Book.Definition_52_4.FundamentalGroup

universe u

/- Proposition 52.1: The path-homotopy classes of loops based at `x₀` form
a group. Its identity is the constant loop class, multiplication is loop
concatenation from left to right, and inversion is path reversal. -/
#check fun {X : Type u} [TopologicalSpace X] (x₀ : X) ↦
  (inferInstance : Group π₁(X, x₀))
#check FundamentalGroup.LeftToRight.one_def
#check FundamentalGroup.LeftToRight.mul_def
#check FundamentalGroup.LeftToRight.inv_def
