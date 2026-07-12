import Mathlib
import Mathlib.Geometry.Manifold.Instances.Sphere
import SmoothManifolds_Lee_2012.Chap01.Sec01.Example_1_8
import SmoothManifolds_Lee_2012.Chap04.Sec04_26.Example_4_35
import SmoothManifolds_Lee_2012.Chap08.Sec08_54.Example_8_2
import SmoothManifolds_Lee_2012.Chap08.Sec08_54.Example_8_4
import SmoothManifolds_Lee_2012.Chap08.Sec08_54.Example_8_5

-- Declarations for this item will be appended below by the statement pipeline.

open scoped ContDiff Manifold Torus

noncomputable section

-- Domain sampling pass:
-- * primary domain: smooth tangent-bundle frames on manifolds;
-- * inspected owner/API declarations: mathlib's `IsLocalFrameOn`,
--   `smooth_chart_coordinate_vector_field`, `circle_angle_vector_field`, and the chapter's torus
--   angle-coordinate vector fields from Example 8.5;
-- * core/canonical owner: `IsLocalFrameOn`;
-- * primitive data: a family of tangent-bundle sections, with smoothness and pointwise basis
--   properties derived through `IsLocalFrameOn` rather than stored in a parallel wrapper API.

section

variable {n : ℕ}

/-- Example 8.10 (1): the standard coordinate vector fields form a smooth global frame for
`ℝⁿ`. -/
theorem example_8_10_euclidean_coordinate_frame (n : ℕ) :
    IsLocalFrameOn (𝓡 n) (EuclideanSpace ℝ (Fin n)) ∞
      (model_coordinate_vector_field
        (⊤ : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin n))))
      Set.univ := sorry

end

section

variable {n : ℕ}
variable {M : Type*} [TopologicalSpace M]
variable [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
variable [IsManifold (𝓡 n) (⊤ : ℕ∞ω) M]

/-- Example 8.10 (2): for any smooth coordinate chart on an `n`-manifold, the associated
coordinate vector fields form a smooth local frame on the chart domain. -/
theorem example_8_10_chart_coordinate_frame
    (e : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
    (he : e ∈ IsManifold.maximalAtlas (𝓡 n) (⊤ : ℕ∞ω) M) :
    IsLocalFrameOn (𝓡 n) (EuclideanSpace ℝ (Fin n)) ∞
      (smooth_chart_coordinate_vector_field e he) Set.univ := sorry

/-- Example 8.10 (3): every point of a smooth manifold lies in the domain of a coordinate frame. -/
theorem example_8_10_point_mem_coordinate_frame_domain (x : M) :
    ∃ (e : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
      (he : e ∈ IsManifold.maximalAtlas (𝓡 n) (⊤ : ℕ∞ω) M),
      x ∈ e.source ∧
        IsLocalFrameOn (𝓡 n) (EuclideanSpace ℝ (Fin n)) ∞
          (smooth_chart_coordinate_vector_field e he) Set.univ := sorry

end

/-- Example 8.10 (4): the circle angle vector field `d / dθ` from Example 8.4 is a smooth global
frame on `S¹`. -/
theorem example_8_10_circle_angle_frame :
    IsLocalFrameOn (𝓡 1) (EuclideanSpace ℝ (Fin 1)) ∞
      (fun _ : Fin 1 ↦ circle_angle_vector_field) Set.univ := sorry

section

variable (n : ℕ)

local notation "TnModel" => ModelWithCorners.pi (fun _ : Fin n ↦ 𝓡 1)
local notation "TnFiber" => Fin n → EuclideanSpace ℝ (Fin 1)
local instance : IsManifold TnModel ∞ (𝕋^{n}) := by infer_instance

/-- Example 8.10 (5): the angle coordinate vector fields
`(∂ / ∂θ¹, ..., ∂ / ∂θⁿ)` on the `n`-torus form a smooth global frame. -/
theorem example_8_10_torus_angle_frame :
    IsLocalFrameOn TnModel TnFiber ∞ (fun i ↦ torus_angle_coordinate_vector_field n i)
      Set.univ := sorry

/- The pullback formula for the torus angle-coordinate vector fields is already provided by the
owner theorem from Example 8.5. -/
#check torus_angle_coordinate_vector_field_apply_standardTorusCovering

end
