import Mathlib
import SmoothManifolds_Lee_2012.Chap05.Sec05_30.Corollary_5_14
import SmoothManifolds_Lee_2012.Chap06.Sec06_44.Definition_6_44_extra_1

-- Declarations for this item will be appended below by the statement pipeline.

open scoped ContDiff Manifold

open Manifold Set

noncomputable section

section

local notation "R2" => EuclideanSpace ℝ (Fin 2)
local notation "R3" => EuclideanSpace ℝ (Fin 3)
local notation "unitSphere2" => Metric.sphere (0 : R3) 1
local notation "sphereR" => Metric.sphere (0 : R3)

/- Radial scaling identifies the unit sphere in `ℝ^3` with the sphere of radius `r > 0`. -/
private noncomputable def positiveSphere_homeomorph (r : ℝ) (hr : 0 < r) :
    unitSphere2 ≃ₜ sphereR r where
  toFun x := ⟨r • (x : R3), by
    rw [mem_sphere_zero_iff_norm, norm_smul, Real.norm_eq_abs, abs_of_pos hr]
    simp [mem_sphere_zero_iff_norm.1 x.2]⟩
  invFun x := ⟨r⁻¹ • (x : R3), by
    rw [mem_sphere_zero_iff_norm, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hr]
    simp [hr.ne', mem_sphere_zero_iff_norm.1 x.2]⟩
  left_inv x := by
    apply Subtype.ext
    simp [smul_smul, hr.ne']
  right_inv x := by
    apply Subtype.ext
    simp [smul_smul, hr.ne']
  continuous_toFun :=
    Continuous.subtype_mk (continuous_const.smul continuous_subtype_val) fun x ↦ by
      rw [mem_sphere_zero_iff_norm, norm_smul, Real.norm_eq_abs, abs_of_pos hr]
      simp [mem_sphere_zero_iff_norm.1 x.2]
  continuous_invFun :=
    Continuous.subtype_mk (continuous_const.smul continuous_subtype_val) fun x ↦ by
      rw [mem_sphere_zero_iff_norm, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hr]
      simp [hr.ne', mem_sphere_zero_iff_norm.1 x.2]

/- The canonical smooth structure on a positive-radius sphere is the transport of the standard
unit-sphere structure along radial scaling. -/
@[reducible]
private noncomputable def positiveSphere_chartedSpace (r : ℝ) (hr : 0 < r) :
    ChartedSpace R2 (sphereR r) :=
  (positiveSphere_homeomorph r hr).isLocalHomeomorph.chartedSpace
    (positiveSphere_homeomorph r hr).surjective

/-- The positive-radius sphere in `ℝ^3` carries the transported smooth `2`-manifold structure. -/
theorem positiveSphere_isManifold (r : ℝ) (hr : 0 < r) :
    let _ : ChartedSpace R2 (sphereR r) := positiveSphere_chartedSpace r hr
    IsManifold (𝓡 2) ∞ (sphereR r) := by
  sorry

/-- The positive-radius sphere in `ℝ^3` is an embedded submanifold with its canonical transported
smooth structure. -/
theorem positiveSphere_isEmbeddedSubmanifold (r : ℝ) (hr : 0 < r) :
    let _ : ChartedSpace R2 (sphereR r) := positiveSphere_chartedSpace r hr
    let _ : IsManifold (𝓡 2) ∞ (sphereR r) := positiveSphere_isManifold r hr
    IsEmbeddedSubmanifold (𝓡 3) (𝓡 2) (sphereR r) := by
  sorry

/-- The map `F : ℝ^2 → ℝ^3` from Problem 6-9, written in Euclidean coordinates. -/
def problem_6_9_map (p : R2) : R3 :=
  WithLp.toLp 2
    ![Real.exp (p 1) * Real.cos (p 0), Real.exp (p 1) * Real.sin (p 0), Real.exp (-p 1)]

/-- The squared radius of the image point `F (x, y)`, simplified to the explicit formula that
depends only on the second coordinate. -/
def problem_6_9_radius_sq (p : R2) : ℝ :=
  Real.exp (2 * p 1) + Real.exp (-2 * p 1)

/-- For a nonnegative radius, the sphere equation `F (x, y) ∈ S_r(0)` is equivalent to the
explicit scalar equation `e^(2y) + e^(-2y) = r^2`. -/
theorem problem_6_9_preimage_eq_radius_sq_level_set (r : ℝ) (hr : 0 ≤ r) :
    problem_6_9_map ⁻¹' sphereR r =
      problem_6_9_radius_sq ⁻¹' {r ^ (2 : ℕ)} := sorry

/-- Helper for Problem 6-9 (1): after rewriting the sphere equation in terms of the scalar
function `e^(2y) + e^(-2y)`, transversality to `S_r(0)` becomes the regular-value condition for
`problem_6_9_radius_sq`. -/
theorem problem_6_9_transverse_to_sphere_iff_regularValue (r : ℝ) (hr : 0 < r) :
    let _ : ChartedSpace R2 (sphereR r) := positiveSphere_chartedSpace r hr
    let _ : IsManifold (𝓡 2) ∞ (sphereR r) := positiveSphere_isManifold r hr
    let _ : IsEmbeddedSubmanifold (𝓡 3) (𝓡 2) (sphereR r) :=
      positiveSphere_isEmbeddedSubmanifold r hr
    IsTransverseToSubmanifold (𝓡 3) (𝓡 2) (𝓡 2) (sphereR r)
      problem_6_9_map ↔
      IsRegularValue (𝓡 2) 𝓘(ℝ, ℝ) problem_6_9_radius_sq (r ^ (2 : ℕ)) := sorry

/-- Helper for Problem 6-9 (1): the explicit scalar function
`problem_6_9_radius_sq (x, y) = e^(2y) + e^(-2y)` has `r^2` as a regular value exactly when
`r ≠ √2`. -/
theorem problem_6_9_radius_sq_isRegularValue_iff (r : ℝ) (hr : 0 < r) :
    IsRegularValue (𝓡 2) 𝓘(ℝ, ℝ) problem_6_9_radius_sq (r ^ (2 : ℕ)) ↔
      r ≠ Real.sqrt 2 := sorry

/-- Problem 6-9 (1): for every positive radius `r`, the map
`F(x, y) = (e^y cos x, e^y sin x, e^{-y})` is transverse to the sphere `S_r(0) ⊆ ℝ^3` exactly
when `r ≠ √2`. -/
theorem problem_6_9_transverse_to_sphere_iff (r : ℝ) (hr : 0 < r) :
    let _ : ChartedSpace R2 (sphereR r) := positiveSphere_chartedSpace r hr
    let _ : IsManifold (𝓡 2) ∞ (sphereR r) := positiveSphere_isManifold r hr
    let _ : IsEmbeddedSubmanifold (𝓡 3) (𝓡 2) (sphereR r) :=
      positiveSphere_isEmbeddedSubmanifold r hr
    IsTransverseToSubmanifold (𝓡 3) (𝓡 2) (𝓡 2) (sphereR r)
      problem_6_9_map ↔
      r ≠ Real.sqrt 2 := sorry

/-- Helper for Problem 6-9 (2): for `r < 0` the sphere `S_r(0)` is empty, while for `r = 0` it
is `{0}`; since `problem_6_9_map` never hits the origin, the preimage is empty throughout
`r ≤ 0`. -/
theorem problem_6_9_preimage_eq_empty_of_nonpos (r : ℝ) (hr : r ≤ 0) :
    problem_6_9_map ⁻¹' sphereR r = ∅ := sorry

/-- Problem 6-9 (2): for every radius `r`, the preimage `F ⁻¹(S_r(0))` carries a
1-dimensional embedded-submanifold structure in `ℝ^2`; for `r ≤ 0` this is the empty
submanifold. -/
theorem problem_6_9_preimage_is_embedded_submanifold (r : ℝ) :
    ∃ (_ : ChartedSpace ℝ (problem_6_9_map ⁻¹' sphereR r))
      (_ : IsManifold 𝓘(ℝ) ∞ (problem_6_9_map ⁻¹' sphereR r)),
      IsEmbeddedSubmanifold (𝓡 2) 𝓘(ℝ)
        (problem_6_9_map ⁻¹' sphereR r) := sorry

end
