import Mathlib
import SmoothManifolds_Lee_2012.Chap04.Sec04_25.Proposition_4_28

-- Declarations for this item will be appended below by the statement pipeline.

-- Semantic search tool unavailable in this environment; the statement below is aligned with the
-- local `Manifold.IsSmoothSubmersion` API from `Proposition_4_28`.

open scoped ContDiff Manifold

namespace Manifold

universe uE uE' uE'' uH uH' uH'' uM uN uP

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {E' : Type uE'} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
variable {E'' : Type uE''} [NormedAddCommGroup E''] [NormedSpace ℝ E'']
variable {H : Type uH} [TopologicalSpace H]
variable {H' : Type uH'} [TopologicalSpace H']
variable {H'' : Type uH''} [TopologicalSpace H'']
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H M]
variable {N : Type uN} [TopologicalSpace N] [ChartedSpace H' N]
variable {P : Type uP} [TopologicalSpace P] [ChartedSpace H'' P]
variable {I : ModelWithCorners ℝ E H} [IsManifold I ∞ M]
variable {J : ModelWithCorners ℝ E' H'} [IsManifold J ∞ N]
variable {K : ModelWithCorners ℝ E'' H''} [IsManifold K ∞ P]

/-- Theorem 4.29 (Characteristic Property of Surjective Smooth Submersions): if
`π : M → N` is a surjective smooth submersion, then a map `F : N → P` is smooth if and only if
`F ∘ π` is smooth. -/
theorem contMDiff_iff_comp_of_surjective_smooth_submersion {π : M → N}
    (hπ : IsSmoothSubmersion I J π) (h_surj : Function.Surjective π) {F : N → P} :
    ContMDiff J K ∞ F ↔ ContMDiff I K ∞ (F ∘ π) := sorry

end Manifold
