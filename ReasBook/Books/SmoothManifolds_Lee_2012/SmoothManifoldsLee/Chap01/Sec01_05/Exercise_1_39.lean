import SmoothManifolds_Lee_2012.SmoothManifoldsLee.Chap01.Sec01_05.Proposition_1_38

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Manifold

universe uM

section

variable {M : Type uM} [TopologicalSpace M] [TopologicalManifoldWithBoundary 0 M]

/- Exercise 1.39: this item asks for proofs of the seven clauses of `Proposition 1.38`.
The core open/closed/complement/boundaryless-equivalence clauses already live in the mathlib
`ModelWithCorners` owner API. The chapter-local source-facing content is the induced
`TopologicalManifold` structure on the canonical interior and boundary submanifolds, together with
their boundaryless companion theorems. -/
#check ModelWithCorners.isOpen_interior
#check manifoldInteriorTopologicalManifold
#check manifoldInterior_boundaryless
#check ModelWithCorners.isClosed_boundary
#check boundaryTopologicalManifold
#check manifoldBoundary_boundaryless
#check ModelWithCorners.Boundaryless.iff_boundary_eq_empty
#check (ModelWithCorners.Boundaryless.boundary_eq_empty : (𝓡 0).boundary M = ∅)
#synth BoundarylessManifold (𝓡 0) M
#check ModelWithCorners.compl_boundary

end
