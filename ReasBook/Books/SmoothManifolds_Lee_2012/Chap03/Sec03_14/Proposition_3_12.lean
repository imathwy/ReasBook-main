import SmoothManifolds_Lee_2012.Chap01.Sec01_06.Definition_1_6_extra_2
import SmoothManifolds_Lee_2012.Chap03.Sec03_14.Proposition_3_10

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Manifold

noncomputable section

universe u

-- Semantic search note: the `lean_leansearch` MCP tool was unavailable in this session, so this
-- file uses the verified local theorem `tangentSpace_finrank_eq_of_n_dimensional_manifold`.

section

variable {n : ℕ} {M : Type u} [TopologicalSpace M] [SmoothManifoldWithBoundary n M]

/-- Proposition 3.12 (Dimension of Tangent Spaces on a Manifold with Boundary). If `M` is an
`n`-dimensional smooth manifold with boundary, then for each `p ∈ M`, the tangent space
`TangentSpace (leeBoundaryModelWithCorners n) p` is an `n`-dimensional real vector space. -/
theorem tangentSpace_finrank_eq_of_smooth_manifold_with_boundary (p : M) :
    Module.finrank ℝ (TangentSpace (leeBoundaryModelWithCorners n) p) = n := sorry

end
