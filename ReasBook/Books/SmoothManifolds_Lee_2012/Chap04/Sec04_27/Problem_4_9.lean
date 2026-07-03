import Mathlib.Geometry.Manifold.Instances.Real
import Mathlib.Tactic.Recall
import SmoothManifolds_Lee_2012.Chap04.Sec04_26.Proposition_4_40

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Manifold ContDiff

universe u v

section

variable {n : ℕ} {M : Type u} {M' : Type v}
variable [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
variable [IsManifold (𝓡 n) ∞ M]
variable [TopologicalSpace M'] {π : M' → M}

/- Problem 4-9 is the boundaryless Euclidean specialization `I = 𝓡 n` of the source-facing
uniqueness theorem `smooth_covering_same_smooth_structure`; the underlying canonical owner of the
uniqueness statement is `IsManifold.maximalAtlas`. -/
recall smooth_covering_same_smooth_structure

end
