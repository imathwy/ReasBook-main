import Mathlib
import Mathlib.Geometry.Manifold.Instances.Sphere
import SmoothManifolds_Lee_2012.SmoothManifoldsLee.Chap01.Sec01.Example_1_8
import SmoothManifolds_Lee_2012.SmoothManifoldsLee.Chap04.Sec04_26.Example_4_35
import SmoothManifolds_Lee_2012.SmoothManifoldsLee.Chap08.Sec08_54.Example_8_4

-- Declarations for this item will be appended below by the statement pipeline.

open scoped ContDiff Manifold Torus

noncomputable section

-- Domain sampling pass:
-- * primary domain: smooth vector fields on the torus and their angle-coordinate description;
-- * inspected owner/API declarations: `Notation_8_54_extra_3` for the canonical bundled smooth
--   vector-field owner `Cₛ^∞⟮I; E, TangentSpace I⟯`, `Example_8_4` for the chapter's angle-field
--   theorem surface, and `Proposition_8_8` for nearby bundled smooth vector-field operations;
-- * source-facing item: the torus angle vector fields `∂ / ∂θⁱ`;
-- * core/canonical owner: bundled smooth tangent-bundle sections, written with
--   `Cₛ^∞⟮I; E, TangentSpace I⟯`;
-- * primitive data is only the vector field family itself, while smoothness is derived from that
--   owner, so no local raw `ContMDiffSection` alias should remain on the public theorem surface.

section

variable (n : ℕ)

local notation "TnModel" => ModelWithCorners.pi (fun _ : Fin n ↦ 𝓡 1)
local notation "SmoothTorusVectorField" =>
  Cₛ^∞⟮TnModel; Fin n → EuclideanSpace ℝ (Fin 1), fun z : 𝕋^{n} ↦ TangentSpace TnModel z⟯
local instance : IsManifold TnModel ∞ (𝕋^{n}) := by infer_instance

/-- The `i`th angle-coordinate vector field `∂ / ∂θⁱ` on the `n`-torus. -/
def torus_angle_coordinate_vector_field (i : Fin n) : SmoothTorusVectorField :=
  ⟨fun z ↦
      show TangentSpace TnModel z from
        ((Pi.single i
            (show EuclideanSpace ℝ (Fin 1) from circle_angle_vector_field (z i))) :
          Fin n → EuclideanSpace ℝ (Fin 1)),
    by sorry⟩

/-- Pulling back the torus angle-coordinate vector field `∂ / ∂θⁱ` along the standard covering
recovers the `i`th standard coordinate basis vector on `ℝⁿ`. -/
@[simp] theorem torus_angle_coordinate_vector_field_apply_standardTorusCovering
    (i : Fin n) (x : EuclideanSpace ℝ (Fin n)) :
    torus_angle_coordinate_vector_field n i (standardTorusCovering n x) =
      mfderiv (𝓡 n) TnModel (standardTorusCovering n) x
        ((NormedSpace.fromTangentSpace x).symm
          ((EuclideanSpace.basisFun (Fin n) ℝ) i)) := sorry

/-- Example 8.5: for the `n`-torus `𝕋ⁿ`, the angle-coordinate vector fields
`∂ / ∂θ¹, ..., ∂ / ∂θⁿ` determined by local angle coordinates are globally defined and smooth.
Concretely, there is a global family of bundled smooth vector fields whose pullback along the
standard covering `standardTorusCovering n : ℝⁿ → 𝕋ⁿ` is the standard coordinate basis on `ℝⁿ`. -/
theorem exists_smooth_torus_angle_coordinate_vector_fields :
    ∃ X : Fin n → SmoothTorusVectorField,
      ∀ (i : Fin n) (x : EuclideanSpace ℝ (Fin n)),
        X i (standardTorusCovering n x) =
          mfderiv (𝓡 n) TnModel (standardTorusCovering n) x
            ((NormedSpace.fromTangentSpace x).symm
              ((EuclideanSpace.basisFun (Fin n) ℝ) i)) := by
  exact ⟨torus_angle_coordinate_vector_field n,
    torus_angle_coordinate_vector_field_apply_standardTorusCovering n⟩

end
