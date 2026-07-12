import Mathlib
import SmoothManifolds_Lee_2012.Chap08.Sec08_60.Definition_8_60_extra_7

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped Quaternion RealInnerProductSpace ContDiff Manifold
open QuaternionAlgebra

-- Domain sampling pass:
-- * primary domain: smooth vector fields and left-invariant frames on the Lie group `S^3` of unit
--   quaternions;
-- * relevant owner declarations inspected before refinement:
--   `VectorField.IsLeftInvariant`,
--   `IsLeftInvariantFrameOn`,
--   `QuaternionAlgebra.Basis.self`,
--   `range_mfderiv_coe_sphere`,
--   `mfderiv_coe_sphere_injective`,
--   and the chapter pattern of keeping ambient coordinate formulas private while exposing
--   intrinsic tangent fields publicly;
-- * best owner abstraction: an intrinsic left-invariant global frame on `unitQuaternionSphere`;
-- * present file status after this pass: the public owner layer is the intrinsic tangent frame on
--   `unitQuaternionSphere`, while the ambient quaternion formulas are private support data and
--   bridge theorems.

local notation "unitQuaternionSphere" => Metric.sphere (0 : ℍ) 1

private abbrev quaternionI : ℍ := (Basis.self ℝ).i
private abbrev quaternionJ : ℍ := (Basis.self ℝ).j
private abbrev quaternionK : ℍ := (Basis.self ℝ).k

local notation "i" => quaternionI
local notation "j" => quaternionJ
local notation "k" => quaternionK

private theorem problem_8_6_finrank_real_quaternion_fact : Fact (Module.finrank ℝ ℍ = 3 + 1) := by
  exact ⟨by simpa using (Quaternion.finrank_eq_four : Module.finrank ℝ ℍ = 4)⟩

attribute [local instance] problem_8_6_finrank_real_quaternion_fact

/-- Problem 8-6 (1): if `p` is imaginary, then for every quaternion `q` the ambient vector `q * p`
lies in the orthogonal complement of `ℝ ∙ q`; when `q` is a unit quaternion, this is the tangent
space of the unit sphere at `q` under the usual identification of tangent vectors in `ℍ` with
ambient vectors. -/
theorem problem_8_6_imaginary_mul_mem_orthogonal {p q : ℍ} (hp : p.re = 0) :
    q * p ∈ (ℝ ∙ q)ᗮ := by
  sorry

/-- The ambient quaternion formula whose restriction to `unitQuaternionSphere` defines `X₁`. -/
private def problem_8_6_X1Ambient : ℍ → ℍ := fun q ↦ q * i

/-- The ambient quaternion formula whose restriction to `unitQuaternionSphere` defines `X₂`. -/
private def problem_8_6_X2Ambient : ℍ → ℍ := fun q ↦ q * j

/-- The ambient quaternion formula whose restriction to `unitQuaternionSphere` defines `X₃`. -/
private def problem_8_6_X3Ambient : ℍ → ℍ := fun q ↦ q * k

private def problem_8_6_tangentOrthogonalEquiv (q : unitQuaternionSphere) :
    TangentSpace (𝓡 3) q ≃ₗ[ℝ] (ℝ ∙ (q : ℍ))ᗮ :=
  let coeMfderiv : TangentSpace (𝓡 3) q →L[ℝ] ℍ :=
    mfderiv (𝓡 3) 𝓘(ℝ, ℍ) ((↑) : unitQuaternionSphere → ℍ) q
  (LinearEquiv.ofInjective coeMfderiv (mfderiv_coe_sphere_injective q)).trans
    (LinearEquiv.ofEq _ _ (range_mfderiv_coe_sphere q))

/-- Problem 8-6 (11): for a unit quaternion `q`, the ambient representative `q i` of `X₁ q` is
tangent to the unit sphere at `q`. -/
theorem problem_8_6_X1_mem_orthogonal (q : unitQuaternionSphere) :
    (q : ℍ) * i ∈ (ℝ ∙ (q : ℍ))ᗮ := by
  sorry

/-- Problem 8-6 (12): for a unit quaternion `q`, the ambient representative `q j` of `X₂ q` is
tangent to the unit sphere at `q`. -/
theorem problem_8_6_X2_mem_orthogonal (q : unitQuaternionSphere) :
    (q : ℍ) * j ∈ (ℝ ∙ (q : ℍ))ᗮ := by
  sorry

/-- Problem 8-6 (13): for a unit quaternion `q`, the ambient representative `q k` of `X₃ q` is
tangent to the unit sphere at `q`. -/
theorem problem_8_6_X3_mem_orthogonal (q : unitQuaternionSphere) :
    (q : ℍ) * k ∈ (ℝ ∙ (q : ℍ))ᗮ := by
  sorry

/-- Problem 8-6 (2): the tangent vector field `X₁` on `S^3`, obtained by restricting right
multiplication by the imaginary unit `i` to the unit quaternion sphere. -/
def problem_8_6_X1 (q : unitQuaternionSphere) : TangentSpace (𝓡 3) q :=
  (problem_8_6_tangentOrthogonalEquiv q).symm
    ⟨problem_8_6_X1Ambient (q : ℍ), problem_8_6_X1_mem_orthogonal q⟩

/-- Problem 8-6 (3): the tangent vector field `X₂` on `S^3`, obtained by restricting right
multiplication by the imaginary unit `j` to the unit quaternion sphere. -/
def problem_8_6_X2 (q : unitQuaternionSphere) : TangentSpace (𝓡 3) q :=
  (problem_8_6_tangentOrthogonalEquiv q).symm
    ⟨problem_8_6_X2Ambient (q : ℍ), problem_8_6_X2_mem_orthogonal q⟩

/-- Problem 8-6 (4): the tangent vector field `X₃` on `S^3`, obtained by restricting right
multiplication by the imaginary unit `k` to the unit quaternion sphere. -/
def problem_8_6_X3 (q : unitQuaternionSphere) : TangentSpace (𝓡 3) q :=
  (problem_8_6_tangentOrthogonalEquiv q).symm
    ⟨problem_8_6_X3Ambient (q : ℍ), problem_8_6_X3_mem_orthogonal q⟩

/-- Problem 8-6 (5): the tangent vector field `X₁` on the unit quaternion sphere is smooth. -/
theorem problem_8_6_X1_contDiff :
    ContMDiff (𝓡 3) (𝓡 3).tangent ∞ (T% problem_8_6_X1) := by
  sorry

/-- Problem 8-6 (6): the tangent vector field `X₂` on the unit quaternion sphere is smooth. -/
theorem problem_8_6_X2_contDiff :
    ContMDiff (𝓡 3) (𝓡 3).tangent ∞ (T% problem_8_6_X2) := by
  sorry

/-- Problem 8-6 (7): the tangent vector field `X₃` on the unit quaternion sphere is smooth. -/
theorem problem_8_6_X3_contDiff :
    ContMDiff (𝓡 3) (𝓡 3).tangent ∞ (T% problem_8_6_X3) := by
  sorry

/-- Problem 8-6 (8): the tangent vector field `X₁` on the unit quaternions is left-invariant. -/
theorem problem_8_6_X1_left_invariant :
    VectorField.IsLeftInvariant problem_8_6_X1 := by
  sorry

/-- Problem 8-6 (9): the tangent vector field `X₂` on the unit quaternions is left-invariant. -/
theorem problem_8_6_X2_left_invariant :
    VectorField.IsLeftInvariant problem_8_6_X2 := by
  sorry

/-- Problem 8-6 (10): the tangent vector field `X₃` on the unit quaternions is left-invariant. -/
theorem problem_8_6_X3_left_invariant :
    VectorField.IsLeftInvariant problem_8_6_X3 := by
  sorry

/-- Problem 8-6 (14): at each unit quaternion `q`, the tangent vectors `X₁ q`, `X₂ q`, and `X₃ q`
are linearly independent, giving the global frame on the unit-quaternion sphere together with the
tangency statements above. -/
theorem problem_8_6_X1_X2_X3_linearIndependent (q : unitQuaternionSphere) :
    LinearIndependent ℝ
      ![problem_8_6_X1 q, problem_8_6_X2 q, problem_8_6_X3 q] := by
  sorry

/-- Problem 8-6: the explicit global frame on `S^3` obtained by restricting the quaternionic vector
fields `X₁`, `X₂`, and `X₃` to the unit sphere. -/
def problem_8_6_frame : Fin 3 → (q : unitQuaternionSphere) → TangentSpace (𝓡 3) q :=
  ![problem_8_6_X1, problem_8_6_X2, problem_8_6_X3]

/-- Problem 8-6 (owner-level companion): intrinsically, the explicit restricted quaternionic frame
`(X₁, X₂, X₃)` is a smooth left-invariant global frame on `unitQuaternionSphere`. This records the
chapter's canonical owner abstraction `IsLeftInvariantFrameOn`, while the ambient quaternion
formulas below are bridge/view statements for the intrinsic frame. -/
theorem problem_8_6_isLeftInvariantFrameOn :
    IsLeftInvariantFrameOn problem_8_6_frame Set.univ := by
  sorry

/-- Problem 8-6 (15): under the ambient coordinate isomorphism `ℍ ≃ₗᵢ[ℝ] ℝ⁴`, the quaternion
formula defining `X₁` has coordinate representation `(-x², x¹, x⁴, -x³)`. -/
theorem problem_8_6_X1_coordinates (q : unitQuaternionSphere) :
    Quaternion.linearIsometryEquivTuple ((q : ℍ) * i) =
      ![-(q : ℍ).imI, (q : ℍ).re, (q : ℍ).imK, -(q : ℍ).imJ] := by
  sorry

/-- Problem 8-6 (16): under the ambient coordinate isomorphism `ℍ ≃ₗᵢ[ℝ] ℝ⁴`, the quaternion
formula defining `X₂` has coordinate representation `(-x³, -x⁴, x¹, x²)`. -/
theorem problem_8_6_X2_coordinates (q : unitQuaternionSphere) :
    Quaternion.linearIsometryEquivTuple ((q : ℍ) * j) =
      ![-(q : ℍ).imJ, -(q : ℍ).imK, (q : ℍ).re, (q : ℍ).imI] := by
  sorry

/-- Problem 8-6 (17): under the ambient coordinate isomorphism `ℍ ≃ₗᵢ[ℝ] ℝ⁴`, the quaternion
formula defining `X₃` has coordinate representation `(-x⁴, x³, -x², x¹)`. -/
theorem problem_8_6_X3_coordinates (q : unitQuaternionSphere) :
    Quaternion.linearIsometryEquivTuple ((q : ℍ) * k) =
      ![-(q : ℍ).imK, (q : ℍ).imJ, -(q : ℍ).imI, (q : ℍ).re] := by
  sorry

end
