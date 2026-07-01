import Mathlib.Geometry.Manifold.IsManifold.InteriorBoundary
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

open Set
open scoped Manifold

universe u𝕜 uE uH uM uE' uH' uN

section

variable {𝕜 : Type u𝕜} [NontriviallyNormedField 𝕜]
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners 𝕜 E H}
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H M]
variable {E' : Type uE'} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
variable {H' : Type uH'} [TopologicalSpace H']
variable {N : Type uN} [TopologicalSpace N] [ChartedSpace H' N]
variable {J : ModelWithCorners 𝕜 E' H'}

/- Proposition 1.45: in the canonical product manifold-with-boundary structure `I.prod J`, if the
left factor is boundaryless, then the boundary of `M × N` is exactly `M × ∂N`. -/
recall ModelWithCorners.boundary_of_boundaryless_left

end
