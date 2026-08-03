module

public import Topology_Munkres_2000.Book.Proposition_52_2

public section

universe u

/- Exercise 52.3. In a path-connected space, `π₁(X, x₀)` is abelian if and only if
basepoint change from `x₀` to `x₁` is independent of the chosen path. -/
#check fun {X : Type u} [TopologicalSpace X] [PathConnectedSpace X] (x₀ x₁ : X) ↦
  (FundamentalGroup.LeftToRight.mulEquivOfPath_independent_iff x₀ x₁).symm
