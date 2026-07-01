import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

open Bundle

section

universe u_𝕜 u_E u_H u_M

variable {𝕜 : Type u_𝕜} [NontriviallyNormedField 𝕜]
variable {E : Type u_E} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {H : Type u_H} [TopologicalSpace H]
variable {I : ModelWithCorners 𝕜 E H}
variable {M : Type u_M} [TopologicalSpace M] [ChartedSpace H M]

/- Definition 3.16-extra-1: the tangent bundle `TM` of a manifold `M` modeled by `I` is the
canonical bundle total space `TangentBundle I M`, i.e. `Bundle.TotalSpace` specialized to the
family `p ↦ TangentSpace I p`; an element is written as a pair `⟨p, v⟩` with
`v : TangentSpace I p`. -/
recall TangentBundle (I : ModelWithCorners 𝕜 E H) (M : Type u_M)
    [TopologicalSpace M] [ChartedSpace H M] : Type _

/- The tangent-bundle projection is the generic bundle projection `TotalSpace.proj`. -/
#check (TotalSpace.proj : TangentBundle I M → M)

end
