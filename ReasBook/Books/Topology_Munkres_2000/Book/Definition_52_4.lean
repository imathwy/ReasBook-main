module

public import Topology_Munkres_2000.Book.Definition_52_4.FundamentalGroup

universe u

/- Definition 52.4: A loop based at `x₀` has type `Path x₀ x₀`. The group
`π₁(X, x₀)` consists of fixed-endpoint path-homotopy classes of such loops,
with multiplication given by left-to-right path traversal. -/
#check FundamentalGroup.LeftToRight
#check fun {X : Type u} [TopologicalSpace X] (x₀ : X) ↦ π₁(X, x₀)
#check fun {X : Type u} [TopologicalSpace X] (x₀ : X) ↦ Path x₀ x₀
#check fun {X : Type u} [TopologicalSpace X] (x₀ : X) ↦ Path.Homotopic.Quotient x₀ x₀
#check fun {X : Type u} [TopologicalSpace X] (x₀ : X) ↦
  (inferInstance : Group π₁(X, x₀))
#check FundamentalGroup.LeftToRight.toPath
#check FundamentalGroup.LeftToRight.fromPath
#check FundamentalGroup.LeftToRight.one_def
#check FundamentalGroup.LeftToRight.mul_def
#check FundamentalGroup.LeftToRight.inv_def
