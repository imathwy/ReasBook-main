import Mathlib.Geometry.Manifold.SmoothEmbedding
import SmoothManifolds_Lee_2012.Chap04.Sec04_27.Problem_4_10

-- Declarations for this item will be appended below by the statement pipeline.

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
