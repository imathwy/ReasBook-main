import Mathlib
import SmoothManifolds_Lee_2012.SmoothManifoldsLee.Chap01.Sec01.Example_1_3

universe uE uF uG uM uN

open Set
open scoped Manifold ContDiff

namespace TopologicalSpace.Opens

variable {M : Type uM} [TopologicalSpace M] {N : Type uN}

/-- The chapter-5 `Opens`-typed graph parametrization is the open-subset view of the canonical
set-typed parametrization from Example 1.3. -/
abbrev graphMap (U : TopologicalSpace.Opens M) (f : M → N) : U → M × N :=
  _root_.graphMap (U : Set M) f

/-- The image of the `Opens`-typed graph parametrization is the graph over the underlying open
set. -/
theorem range_graphMap_eq_graphOn (U : TopologicalSpace.Opens M) (f : M → N) :
    Set.range (graphMap U f) = (U : Set M).graphOn f := sorry

end TopologicalSpace.Opens

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {F : Type uF} [NormedAddCommGroup F] [NormedSpace ℝ F]
variable {G : Type uG} [TopologicalSpace G] {J : ModelWithCorners ℝ F G}
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace E M]
variable {N : Type uN} [TopologicalSpace N] [ChartedSpace G N]
variable [IsManifold (modelWithCornersSelf ℝ E) (∞ : ℕ∞ω) M]
variable [IsManifold J (∞ : ℕ∞ω) N]

/-- Proposition 5.4: for a smooth map on an open subset of a smooth manifold without boundary, the
canonical graph parametrization into the product manifold is a smooth embedding, so its image is an
embedded submanifold of the ambient product. -/
-- Proof sketch: the map `x ↦ (x, f x)` is smooth by combining the inclusion of the open subset
-- with `f`; the first projection is a left inverse, so the differential is injective and the map
-- is an immersion. The first projection also gives a continuous inverse from the image back to the
-- domain, so the map is a topological embedding.
theorem graphMap_isSmoothEmbedding (U : TopologicalSpace.Opens M) (f : M → N)
    (hf : ContMDiffOn (modelWithCornersSelf ℝ E) J (⊤ : WithTop ℕ∞) f U) :
    Manifold.IsSmoothEmbedding (modelWithCornersSelf ℝ E)
      ((modelWithCornersSelf ℝ E).prod J) (⊤ : WithTop ℕ∞) (TopologicalSpace.Opens.graphMap U f) :=
  sorry
