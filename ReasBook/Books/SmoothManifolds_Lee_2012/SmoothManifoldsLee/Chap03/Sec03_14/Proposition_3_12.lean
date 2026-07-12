import Mathlib.Tactic.Recall
import SmoothManifolds_Lee_2012.Chap03.Sec03_14.Proposition_3_10

-- Declarations for this item will be appended below by the statement pipeline.

-- Domain sampling pass: this item lies in the smooth-manifold tangent-space / dimension API.
-- Layer triage:
-- `source-facing`: Proposition 3.12 is the boundary-model specialization of the tangent-space
-- dimension statement.
-- `core/canonical`: `TangentSpace` and `Module.finrank` are the owner-level mathlib notions, and
-- the project theorem `tangentSpace_finrank_eq_of_n_dimensional_manifold` is the canonical chapter
-- owner theorem.
-- `bridge/view`: the boundary-specific statement follows by specializing the manifold model to
-- `leeBoundaryModelWithCorners n` through the `SmoothManifoldWithBoundary` instance.
-- Relevant declarations checked before refinement:
-- `TangentSpace`,
-- `Module.finrank`,
-- `SmoothManifoldWithBoundary`,
-- `tangentSpace_finrank_eq_of_n_dimensional_manifold`.
-- Primitive data is only the manifold model and the point. The boundary-specific theorem is
-- derived API, so this chapter file should center the core owner theorem instead of the duplicate
-- section-level specialization.

/- Proposition 3.12 (Dimension of Tangent Spaces on a Manifold with Boundary). The chapter-level
boundary statement is the specialization of the core tangent-space dimension theorem
`tangentSpace_finrank_eq_of_n_dimensional_manifold` to Lee's boundary model. -/
recall tangentSpace_finrank_eq_of_n_dimensional_manifold
