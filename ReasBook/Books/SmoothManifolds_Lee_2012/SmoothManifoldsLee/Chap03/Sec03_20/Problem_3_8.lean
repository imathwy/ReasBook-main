import SmoothManifolds_Lee_2012.Chap03.Sec03_18.Definition_3_18_extra_3
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Manifold ContDiff

universe u v

section

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : Type v} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [BoundarylessManifold I M]

/- Problem 3-8: the smooth-curve realization of tangent vectors at `p` is already exposed
upstream as the canonical equivalence `curveVelocityClassEquivTangentSpace`. -/
recall curveVelocityClassEquivTangentSpace {E : Type u} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {H : Type v} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type u} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [BoundarylessManifold I M] (p : M) :
    CurveVelocityClass I p ≃ TangentSpace I p

end
