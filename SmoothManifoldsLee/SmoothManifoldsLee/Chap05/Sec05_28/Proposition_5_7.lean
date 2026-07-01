import Mathlib
import SmoothManifoldsLee.Chap05.Sec05_28.Definition_5_28_extra_2

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Manifold ContDiff

universe uE uF uG uM uN

-- Semantic search tool unavailable in this environment; the statement shape was checked against
-- the local graph API in `Proposition_5_4`, the set-level owner `Set.IsProperlyEmbedded`, and
-- mathlib's Hausdorff left-inverse closed-range API.

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {F : Type uF} [NormedAddCommGroup F] [NormedSpace ℝ F]
variable {G : Type uG} [TopologicalSpace G] {J : ModelWithCorners ℝ F G}
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace E M] [T2Space M]
variable {N : Type uN} [TopologicalSpace N] [ChartedSpace G N]
variable [IsManifold (modelWithCornersSelf ℝ E) (∞ : ℕ∞ω) M]
variable [IsManifold J (∞ : ℕ∞ω) N]

/-- Proposition 5.7 (Global Graphs Are Properly Embedded): if `f : M → N` is smooth, then its
global graph in `M × N` is properly embedded. Combined with Proposition 5.4, this identifies the
global graph as a properly embedded smooth submanifold of the product manifold. -/
theorem smooth_map_graph_isProperlyEmbedded {f : M → N}
    (hf : ContMDiff (modelWithCornersSelf ℝ E) J ∞ f) :
    (Set.univ.graphOn f).IsProperlyEmbedded := sorry
