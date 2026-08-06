import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap21.Definition_21_2_2
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap21.Proposition_21_4_2

open ROrientedManifoldWithBoundary
open scoped Manifold

noncomputable section

section

variable {W : Type} [TopologicalSpace W] [CompactSpace W]

private instance boundaryModel_finrank_fact (k : ℕ) :
    Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (4 * k))) = 4 * k) :=
  ⟨@finrank_euclideanSpace_fin ℝ _ (4 * k)⟩

/-- Theorem 21.5.1. If `M = ∂W` for a compact oriented `(4 * k + 1)`-manifold-with-boundary `W`,
then `I(M) = 0`. Here the source manifold `M` is formalized by the boundary subtype
`manifoldBoundary (4 * k + 1) W`, its induced orientation by
`toBoundaryROrientedManifoldSucc ℤ (4 * k) W`, and the index `I(M)` by
`manifoldIndex`. -/
theorem manifoldIndex_boundary_eq_zero (k : ℕ)
    [ChartedSpace (EuclideanHalfSpace (4 * k + 1)) W]
    [ROrientedManifoldWithBoundary ℤ (4 * k + 1) W]
    [ChartedSpace (EuclideanSpace ℝ (Fin (4 * k))) (manifoldBoundary (4 * k + 1) W)] :
    manifoldIndex (toBoundaryROrientedManifoldSucc ℤ (4 * k) W) = 0 := by
  sorry

end
