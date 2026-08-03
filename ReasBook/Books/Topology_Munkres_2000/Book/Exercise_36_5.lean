module

public import Topology_Munkres_2000.Book.Exercise_36_5.Charts
public import Topology_Munkres_2000.Book.Exercise_36_5.Instances
public import Topology_Munkres_2000.Book.Exercise_36_5.Separation

public section

open Set

/- Exercise 36.5 (1). The designated sets form a basis for the topology. -/
#check LineWithTwoOrigins.basis_isTopologicalBasis

/- Exercise 36.5 (2). Deleting either origin gives a space homeomorphic to `ℝ`. -/
#check LineWithTwoOrigins.removeOriginHomeomorphReal

/- Exercise 36.5 (3). The line with two origins satisfies the `T₁` axiom. -/
#check LineWithTwoOrigins.instT1Space

/- Exercise 36.5 (4). The line with two origins is not Hausdorff. -/
#check LineWithTwoOrigins.notHausdorff

/- Exercise 36.5 (5). The line with two origins has a countable topological basis. -/
#check LineWithTwoOrigins.instSecondCountableTopology

namespace LineWithTwoOrigins

/-- Exercise 36.5 (6). Every point has an open neighborhood homeomorphic to an open subset of
`EuclideanSpace ℝ (Fin 1)`. -/
theorem locallyEuclideanOneDimensional (x : LineWithTwoOrigins) :
    ∃ U : Set LineWithTwoOrigins, And (IsOpen U) (And (x ∈ U)
      (∃ V : Set (EuclideanSpace ℝ (Fin 1)), And (IsOpen V) (Nonempty (U ≃ₜ V)))) := by
  -- Use the preferred chart to choose compatible open neighborhoods in the space and model.
  let e := chartAt (EuclideanSpace ℝ (Fin 1)) x
  refine ⟨e.source, e.open_source, mem_chart_source (EuclideanSpace ℝ (Fin 1)) x, e.target, ?_⟩
  -- Restricting the partial homeomorphism gives the required homeomorphism of subspaces.
  exact ⟨e.open_target, Nonempty.intro e.toHomeomorphSourceTarget⟩

end LineWithTwoOrigins

/- The local Euclidean conclusion is also available as the canonical one-dimensional
charted-space instance. -/
#check LineWithTwoOrigins.instChartedSpace
