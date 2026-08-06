import Mathlib.Geometry.Manifold.Instances.Real
import Mathlib.LinearAlgebra.Dimension.Finrank
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap13.IntegralSingularHomology
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap20.Definition_20_1_1

open scoped Manifold Topology

noncomputable section

section

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {H : Type} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
variable {M : Type} [TopologicalSpace M] [T2Space M] [CompactSpace M] [ConnectedSpace M]
variable [ChartedSpace H M] [IsManifold I ⊤ M] [Fact (Module.finrank ℝ E = 3)]

/-- Problem 21.6.5: if `M` is a closed nonorientable `3`-manifold, then `H_1(M; ℤ)` is infinite.
In the current local API, nonorientability is expressed directly by
`¬ Nonempty (ROrientedManifold ℤ I 3 M)`, while the ambient smooth `3`-manifold hypotheses are
recorded by `[IsManifold I ⊤ M]` together with `[Fact (Module.finrank ℝ E = 3)]`. -/
theorem firstIntegralSingularHomology_infinite_of_closed_nonorientableThreeManifold
    (h_nonorientable : ¬ Nonempty (ROrientedManifold ℤ I 3 M)) :
    Infinite (integralSingularHomology 1 (TopCat.of M)) := by
  -- TODO: complete the odd-prime coefficient argument from the source after the canonical
  -- universal-coefficient and Euler-characteristic owners are connected in the local API.
  sorry

end
