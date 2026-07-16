import SmoothManifolds_Lee_2012.SmoothManifoldsLee.Chap04.Sec04_23.Theorem_4_12

-- Declarations for this item will be appended below by the statement pipeline.

-- Semantic search tool unavailable in this environment; local precedents used:
-- `Manifold.HasConstantRank` from `Exercise_4_4` and the rank-theorem normal-form API in
-- `Theorem_4_12`.

open Set
open scoped ContDiff Manifold

universe uM uN

section

variable {m n : ℕ}
variable {M : Type uM} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin m)) M]
  [IsManifold (𝓘(ℝ, EuclideanSpace ℝ (Fin m))) ∞ M]
variable {N : Type uN} [TopologicalSpace N]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) N]
  [IsManifold (𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ N]

local notation "I_m" => 𝓘(ℝ, EuclideanSpace ℝ (Fin m))
local notation "I_n" => 𝓘(ℝ, EuclideanSpace ℝ (Fin n))

/-- A local linear coordinate representation of `F` at `p` consists of smooth source and target
charts around `p` and `F p` in which the coordinate representative of `F` agrees with a linear
map on the source chart target. -/
structure LinearCoordinateRepresentationAt (F : M → N) (p : M) where
  domChart : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin m))
  codChart : OpenPartialHomeomorph N (EuclideanSpace ℝ (Fin n))
  domChart_mem_maximalAtlas :
    domChart ∈ IsManifold.maximalAtlas I_m ∞ M
  codChart_mem_maximalAtlas :
    codChart ∈ IsManifold.maximalAtlas I_n ∞ N
  point_mem_dom : p ∈ domChart.source
  image_mem_cod : F p ∈ codChart.source
  linearMap : EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin n)
  mapsTo : MapsTo F domChart.source codChart.source
  eqOn : EqOn (codChart ∘ F ∘ domChart.symm) linearMap domChart.target

variable [ConnectedSpace M]

/-- Corollary 4.13: for a smooth map on a connected smooth manifold, having a linear coordinate
representation near each point is equivalent to having constant rank. -/
theorem locally_linear_in_coordinates_iff_exists_constant_rank {F : M → N}
    (hF : ContMDiff I_m I_n ∞ F) :
    (∀ p : M, Nonempty (@LinearCoordinateRepresentationAt m n M _ _ N _ _ F p)) ↔
      ∃ r : ℕ, Manifold.HasConstantRank I_m I_n F r := sorry

end
