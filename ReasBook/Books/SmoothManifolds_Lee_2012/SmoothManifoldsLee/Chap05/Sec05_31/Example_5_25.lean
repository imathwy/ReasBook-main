import SmoothManifolds_Lee_2012.SmoothManifoldsLee.Chap05.Sec05_28.Proposition_5_4
import SmoothManifolds_Lee_2012.SmoothManifoldsLee.Chap05.Sec05_31.Definition_5_31_extra_2

open scoped ContDiff Manifold
open Manifold

/- Example 5.25 is organized around the immersed-submanifold parametrization owner introduced in
§5.31. -/
#check ImmersedSubmanifold.IsGlobalParametrization

/- A smooth embedding canonically determines the corresponding immersed submanifold. -/
#check IsSmoothEmbedding.toImmersedSubmanifold

/- The graph parametrization itself is the canonical open-subset map `U → ℝ^n × ℝ^k`. -/
#check TopologicalSpace.Opens.graphMap

/- Proposition 5.4 upgrades that same graph parametrization to a smooth embedding. -/
#check graphMap_isSmoothEmbedding

/- The image of the graph parametrization is the graph over `U`. -/
#check TopologicalSpace.Opens.range_graphMap_eq_graphOn

/-- Example 5.25: for a smooth map on an open subset of `ℝ^n`, the canonical graph map is a
global parametrization of the immersed submanifold canonically induced by the corresponding smooth
embedding into `ℝ^n × ℝ^k`. -/
theorem graphMap_isGlobalParametrization {n k : ℕ}
    (U : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin n)))
    (f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin k))
    (hf : ContDiffOn ℝ (⊤ : WithTop ℕ∞) f (U : Set (EuclideanSpace ℝ (Fin n)))) :
    ((graphMap_isSmoothEmbedding U f hf.contMDiffOn).toImmersedSubmanifold).IsGlobalParametrization
      U (U.graphMap f) := by
  refine ⟨fun u ↦ u, rfl, Topology.IsOpenEmbedding.id, Function.surjective_id⟩
