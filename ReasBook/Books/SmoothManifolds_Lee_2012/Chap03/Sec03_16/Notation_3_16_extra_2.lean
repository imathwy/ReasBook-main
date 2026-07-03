import Mathlib.Geometry.Manifold.VectorBundle.Tangent

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Manifold

section

universe u_𝕜 u_E u_H u_M

variable {𝕜 : Type u_𝕜} [NontriviallyNormedField 𝕜]
variable {E : Type u_E} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {H : Type u_H} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
variable {M : Type u_M} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]

/- Notation 3.16-extra-2: the natural coordinates on `TM = TangentBundle I M` are the canonical
charts of the tangent bundle with values in `ModelProd H E`, namely the chart family
`chartAt (ModelProd H E)`. -/
#check (chartAt (ModelProd H E) : TangentBundle I M → _)

end
