import Mathlib.Geometry.Manifold.SmoothEmbedding

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Corollary_4_13 (from Chap04/Sec04_23) -/
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

/-! ### Problem_4_13 (from Chap04/Sec04_27) -/
-- Semantic search tool unavailable in this environment; local chapter precedent around
-- `sphereToRealProjectiveSpace` and descended smooth embeddings was checked directly.

open Manifold
open scoped Manifold Matrix

noncomputable section

local notation "R2" => EuclideanSpace ℝ (Fin 2)
local notation "R3" => EuclideanSpace ℝ (Fin 3)
local notation "R4" => EuclideanSpace ℝ (Fin 4)

/-- Helper for the real-projective-plane embedding problem: the sphere-level map
`(x, y, z) ↦ (x² - y², xy, xz, yz)` from `S²` to `ℝ⁴`. -/
def real_projective_plane_embedding_lift :
    Metric.sphere (0 : R3) 1 → R4 :=
  fun p ↦
    let x := (p : R3) 0
    let y := (p : R3) 1
    let z := (p : R3) 2
    EuclideanSpace.single 0 (x ^ (2 : ℕ) - y ^ (2 : ℕ)) +
      EuclideanSpace.single 1 (x * y) +
      EuclideanSpace.single 2 (x * z) +
      EuclideanSpace.single 3 (y * z)

/-- Helper for the real-projective-plane embedding problem: the sphere-level lift has the stated
coordinate formula. -/
theorem real_projective_plane_embedding_lift_apply
    (p : Metric.sphere (0 : R3) 1) :
    real_projective_plane_embedding_lift p =
      EuclideanSpace.single 0 (((p : R3) 0) ^ (2 : ℕ) - ((p : R3) 1) ^ (2 : ℕ)) +
        EuclideanSpace.single 1 (((p : R3) 0) * ((p : R3) 1)) +
        EuclideanSpace.single 2 (((p : R3) 0) * ((p : R3) 2)) +
        EuclideanSpace.single 3 (((p : R3) 1) * ((p : R3) 2)) := sorry

/-- Problem 4-13: the map `(x, y, z) ↦ (x² - y², xy, xz, yz)` on `S²` descends through the
quotient map `sphereToRealProjectiveSpace 2 : S² → ℝP²` to a smooth embedding of `ℝP²` into
`ℝ⁴`. -/
theorem real_projective_plane_exists_isSmoothEmbedding_to_R4
    [ChartedSpace R2 (RealProjectiveSpace 2)]
    [IsManifold (𝓡 2) (⊤ : WithTop ℕ∞) (RealProjectiveSpace 2)] :
    ∃ f : RealProjectiveSpace 2 → R4,
      ((∀ p : Metric.sphere (0 : R3) 1,
          f (sphereToRealProjectiveSpace 2 p) = real_projective_plane_embedding_lift p) ∧
        Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 4) (⊤ : WithTop ℕ∞) f) := sorry
