import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import SmoothManifolds_Lee_2012.Chap08.Sec08_57.Definition_8_57_extra_1
import SmoothManifolds_Lee_2012.Chap08.Sec08_57.Example_8_17_extra_1

open scoped ContDiff Manifold
open NormedSpace

noncomputable section

local notation "Plane" => ℝ × ℝ

-- Domain sampling pass: this source-facing example lives in the smooth-manifold tangent-space /
-- vector-field domain. Relevant owner declarations checked before refinement:
-- `NormedSpace.fromTangentSpace` (core/canonical tangent-space owner),
-- `VectorField.f_related` from the chapter (source-facing relatedness owner),
-- `Example_8_3.euler_vector_field` as a project precedent for building Euclidean-model vector
-- fields via `(fromTangentSpace x).symm`,
-- and Proposition 8.16's `f_related_iff_mfderiv_comp_eq` as the chapter's derived API.
-- Primitive data here is only the map `t ↦ (cos t, sin t)` and the two dependent sections
-- `∀ p, TangentSpace _ p`; the coordinate formulas are derived through `fromTangentSpace`.

/-- The circle parametrization `F(t) = (cos t, sin t)` from `ℝ` to `ℝ²`. -/
def example_8_17_circle_parametrization : ℝ → Plane :=
  fun t ↦ (Real.cos t, Real.sin t)

/-- Coordinate formula for `example_8_17_circle_parametrization`. -/
@[simp]
theorem example_8_17_circle_parametrization_apply (t : ℝ) :
    example_8_17_circle_parametrization t = (Real.cos t, Real.sin t) := rfl

/-- The circle parametrization from Example 8.17 is smooth. -/
theorem example_8_17_circle_parametrization_contMDiff :
    ContMDiff 𝓘(ℝ) 𝓘(ℝ, Plane) ∞ example_8_17_circle_parametrization := by
  -- Smoothness on the product target is coordinatewise from the smooth sine and cosine maps.
  simpa [example_8_17_circle_parametrization] using
    (Real.contDiff_cos.contMDiff.prodMk Real.contDiff_sin.contMDiff)

/-- The planar rotation vector field `Y = x ∂/∂y - y ∂/∂x` from Example 8.17. -/
def example_8_17_rotation_field (p : Plane) : TangentSpace 𝓘(ℝ, Plane) p :=
  (fromTangentSpace p).symm (-p.2, p.1)

/-- Under the canonical tangent-space identification, `example_8_17_d_dt` has coordinate value
`1`. -/
@[simp] theorem fromTangentSpace_example_8_17_d_dt (t : ℝ) :
    fromTangentSpace t (example_8_17_d_dt t) = 1 := by
  simp [example_8_17_d_dt]

/-- Under the canonical tangent-space identification, `example_8_17_rotation_field` has
coordinate formula `(-y, x)`. -/
@[simp] theorem fromTangentSpace_example_8_17_rotation_field (p : Plane) :
    fromTangentSpace p (example_8_17_rotation_field p) = (-p.2, p.1) := by
  simp [example_8_17_rotation_field]

/-- Helper for Example 8.17: the ordinary derivative of the circle parametrization sends the
unit tangent coordinate to `(-sin t, cos t)`. -/
lemma circleParametrizationFderivApplyOne (t : ℝ) :
    fderiv ℝ example_8_17_circle_parametrization t 1 = (-Real.sin t, Real.cos t) := by
  -- Differentiate the cosine and sine coordinates separately and recombine them.
  have hpair :
      HasDerivAt example_8_17_circle_parametrization (-Real.sin t, Real.cos t) t := by
    simpa [example_8_17_circle_parametrization] using
      (Real.hasDerivAt_cos t).prodMk (Real.hasDerivAt_sin t)
  -- Evaluating the Fréchet derivative at the unit vector recovers the velocity pair.
  exact DFunLike.congr_fun hpair.hasFDerivAt.fderiv 1

/-- Helper for Example 8.17: the circle parametrization pushes `d / dt` forward to the planar
rotation field at each parameter value. -/
lemma circleParametrizationPushforwardDdt (t : ℝ) :
    mfderiv 𝓘(ℝ) 𝓘(ℝ, Plane) example_8_17_circle_parametrization t (example_8_17_d_dt t) =
      example_8_17_rotation_field (example_8_17_circle_parametrization t) := by
  -- Compare tangent vectors through the canonical Euclidean coordinates at `F t`.
  apply (fromTangentSpace (example_8_17_circle_parametrization t)).injective
  -- Route correction: instead of unfolding the vector fields in the target theorem, compute the
  -- pushforward once in coordinates and match it to the named rotation-field formula.
  have hpush :
      fromTangentSpace (example_8_17_circle_parametrization t)
        (mfderiv 𝓘(ℝ) 𝓘(ℝ, Plane) example_8_17_circle_parametrization t
          (example_8_17_d_dt t)) =
        (-Real.sin t, Real.cos t) := by
    simpa [mfderiv_eq_fderiv] using circleParametrizationFderivApplyOne t
  -- Along the circle, the rotation field has the same coordinate expression.
  simpa [example_8_17_circle_parametrization] using
    hpush.trans
      (fromTangentSpace_example_8_17_rotation_field
        (example_8_17_circle_parametrization t)).symm

/-- Example 8.17: if `F(t) = (cos t, sin t)`, then the vector field `d/dt` on `ℝ` is
`F`-related to the vector field `Y = x ∂/∂y - y ∂/∂x` on `ℝ²`. -/
theorem example_8_17_d_dt_related_rotation_field :
    VectorField.f_related
      example_8_17_circle_parametrization
      example_8_17_d_dt
      example_8_17_rotation_field := by
  constructor
  · -- The relation packages the smoothness of the circle parametrization itself.
    exact example_8_17_circle_parametrization_contMDiff
  · -- Pointwise, the differential sends `d / dt` to the rotation field along the image circle.
    intro t
    exact circleParametrizationPushforwardDdt t
