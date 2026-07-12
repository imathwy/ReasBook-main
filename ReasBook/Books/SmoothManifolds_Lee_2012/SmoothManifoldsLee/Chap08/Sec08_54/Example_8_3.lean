import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Geometry.Manifold.Instances.Real
import Mathlib.Geometry.Manifold.IsManifold.Basic
import Mathlib.Geometry.Manifold.VectorBundle.Tangent

-- Declarations for this item will be appended below by the statement pipeline.

open scoped ContDiff Manifold
open NormedSpace

noncomputable section

-- Semantic recall note: `lean_leansearch` was unavailable in this environment, so this item uses
-- the canonical owner `NormedSpace.fromTangentSpace` for the Euler vector field on a real model
-- space and then specializes the source-facing Example 8.3 statements to Euclidean spaces.

section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Example 8.3 (1): the Euler vector field on a real normed vector space is the vector field
whose value at `x : E` is the tangent vector corresponding to `x` itself under the canonical
identification `TangentSpace 𝓘(ℝ, E) x ≃L[ℝ] E`. For `E = EuclideanSpace ℝ (Fin n)`, this is the
usual Euler vector field on `ℝⁿ`, with standard-coordinate formula `∑ i, x i ∂/∂xⁱ|ₓ`. -/
def euler_vector_field (x : E) : TangentSpace 𝓘(ℝ, E) x :=
  x

/-- Under the canonical tangent-space identification, the Euler vector field has coordinate vector
equal to the base point. -/
@[simp] theorem fromTangentSpace_euler_vector_field (x : E) :
    fromTangentSpace x (euler_vector_field x) = x := by
  -- On a model vector space, `fromTangentSpace` is definitionally the identity.
  rfl

end

section

variable (n : ℕ)

/-- Example 8.3 (2): the Euler vector field is smooth because its coordinate functions are
linear. -/
theorem euler_vector_field_smooth :
    ContMDiff (𝓡 n) (𝓡 n).tangent ∞
      (T% (euler_vector_field : ∀ x : EuclideanSpace ℝ (Fin n), TangentSpace (𝓡 n) x)) := by
  -- Reduce manifold smoothness on the model space to ordinary smoothness of the vector field.
  rw [contMDiff_vectorSpace_iff_contDiff]
  -- The Euler field is definitionally the identity map on the model vector space.
  simpa [euler_vector_field] using
    (contDiff_id : ContDiff ℝ ∞ (fun x : EuclideanSpace ℝ (Fin n) ↦ x))

/-- Example 8.3 (3): the Euler vector field vanishes at the origin. -/
theorem euler_vector_field_at_origin :
    euler_vector_field (0 : EuclideanSpace ℝ (Fin n)) = 0 := by
  -- The Euler field is the identity map on the model vector space.
  rfl

/-- Example 8.3 (4): under the canonical tangent-space identification, the Euler vector field is a
positive scalar multiple of the radial direction at every point, hence away from the origin it
points radially outward. -/
theorem euler_vector_field_points_radially_outward
    (x : EuclideanSpace ℝ (Fin n)) :
    ∃ a : ℝ, 0 < a ∧
      fromTangentSpace x (euler_vector_field x) = a • x := by
  refine ⟨1, zero_lt_one, ?_⟩
  simp

end
