import Mathlib.Geometry.Manifold.IsManifold.InteriorBoundary
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Manifold

universe u𝕜 uE uH uM

section

variable {𝕜 : Type u𝕜} [NontriviallyNormedField 𝕜]
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners 𝕜 E H}
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H M]

/- Theorem 1.37 (source-facing/core-canonical): in the manifold-with-boundary API, the theorem that
the manifold interior and boundary are disjoint is exactly
`ModelWithCorners.disjoint_interior_boundary`. The complement identity
`ModelWithCorners.compl_boundary` is derived API in the same namespace. -/
recall ModelWithCorners.disjoint_interior_boundary

end
