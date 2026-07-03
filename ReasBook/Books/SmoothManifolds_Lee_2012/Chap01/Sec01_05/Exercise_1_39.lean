import SmoothManifolds_Lee_2012.Chap01.Sec01_05.Proposition_1_38
import SmoothManifolds_Lee_2012.Chap01.Sec01_05.Theorem_1_37

-- Declarations for this item will be appended below by the statement pipeline.

open TopologicalSpace
open scoped Manifold

universe uM

section

variable {M : Type uM} [TopologicalSpace M] [TopologicalManifoldWithBoundary 0 M]

/- Exercise 1.39: this item asks for proofs of the seven clauses of `Proposition 1.38`.
In the textbook argument, topological invariance of the boundary is used in the chart-independence
steps for the manifold-structure statements on the interior and boundary, namely parts `(2)` and
`(4)`, and thus also enters the equivalence in part `(5)`. The refined file keeps the induced
`TopologicalManifold` owners for the canonical interior and boundary submanifolds as the main
public surface and exposes
boundarylessness only as the companion theorem. -/
#check manifoldInterior_isOpen
#check manifoldInteriorTopologicalManifold
#check manifoldInterior_boundaryless
#check manifoldBoundary_isClosed
#check boundaryTopologicalManifold
#check manifoldBoundary_boundaryless
#check ModelWithCorners.Boundaryless.iff_boundary_eq_empty
#check (ModelWithCorners.Boundaryless.boundary_eq_empty : (𝓡 0).boundary M = ∅)
#synth BoundarylessManifold (𝓡 0) M
#check ModelWithCorners.compl_boundary

end
