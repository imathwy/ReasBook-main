import Mathlib.Geometry.Manifold.MFDeriv.Tangent
import Mathlib.Tactic.Recall

open Bundle
open scoped Manifold

section

universe u𝕜 uE uH uM

variable {𝕜 : Type u𝕜} [NontriviallyNormedField 𝕜]
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners 𝕜 E H}
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]

-- Declarations for this item will be appended below by the statement pipeline.

/- Remark 3.15-extra-5: in Lean, the coordinate vectors attached to a local coordinate system are
encoded by the differential of the inverse chart map on the tangent bundle. Thus the vector
corresponding to the `i`-th coordinate direction is determined by the whole inverse chart, not by
the single coordinate function `x^i` alone; changing the remaining coordinate functions can change
the resulting tangent vector. This chart-level dependence is expressed by
`tangentMap_chart_symm`. -/
recall tangentMap_chart_symm {p : TangentBundle I M} {q : TangentBundle I H}
    (h : q.1 ∈ (chartAt H p.1).target) :
    tangentMap I I (chartAt H p.1).symm q =
      (chartAt (ModelProd H E) p).symm (TotalSpace.toProd H E q)

end
