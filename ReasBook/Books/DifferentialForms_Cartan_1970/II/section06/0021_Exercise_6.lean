import Mathlib
import DifferentialForms_Cartan_1970.II.section05.«0027_Remark_II_1_extra_17»

-- Declarations for this item will be appended below by the statement pipeline.

open scoped unitInterval

noncomputable section

/-- Rescale the real and imaginary coordinates of a complex number by `a` and `b`. -/
private def ellipseAxisMap (a b : ℝ) : ℂ → ℂ :=
  fun z ↦ a * z.re + (b * z.im) * Complex.I

/-- A concrete parametrization of the axis-scaled unit circle with horizontal parameter `a` and
vertical parameter `b`. -/
def ellipseParam (a b : ℝ) : ℝ → ℂ :=
  ellipseAxisMap a b ∘ circleMap 0 1

private theorem ellipseAxisMap_continuous (a b : ℝ) : Continuous (ellipseAxisMap a b) := by
  simpa [ellipseAxisMap] using
    (by
      fun_prop :
        Continuous fun z : ℂ ↦ a * z.re + (b * z.im) * Complex.I)

@[simp] private theorem ellipseAxisMap_one (a b : ℝ) :
    ellipseAxisMap a b (1 : ℂ) = (a : ℂ) := by
  simp [ellipseAxisMap]

@[simp] theorem ellipseParam_apply (a b t : ℝ) :
    ellipseParam a b t = a * Real.cos t + (b * Real.sin t) * Complex.I := by
  simp [ellipseParam, ellipseAxisMap, circleMap_zero_re, circleMap_zero_im]

/-- The axis-scaled image of the positively oriented unit circle, viewed as a closed path. -/
abbrev ellipsePath (a b : ℝ) : Path (a : ℂ) (a : ℂ) :=
  ((closedDiscBoundaryPath (1 : NNReal)
      (⟨Subtype.val, continuous_subtype_val⟩ : C(Metric.closedBall (0 : ℂ) (1 : ℝ), ℂ))).map
      (ellipseAxisMap_continuous a b)).cast
    (ellipseAxisMap_one a b).symm
    (ellipseAxisMap_one a b).symm

@[simp] theorem ellipsePath_apply (a b : ℝ) (t : I) :
    ellipsePath a b t = ellipseParam a b (2 * Real.pi * (t : ℝ)) := by
  simp [ellipsePath, ellipseParam]
  simpa using congrArg (ellipseAxisMap a b)
    (closedDiscBoundaryPath_apply (1 : NNReal)
      (⟨Subtype.val, continuous_subtype_val⟩ : C(Metric.closedBall (0 : ℂ) (1 : ℝ), ℂ)) t)

/-- For nonzero axis parameters `a` and `b`, the closed path `ellipsePath a b` traces exactly the
ellipse cut out by the quadratic equation with semiaxes `|a|` and `|b|`. -/
-- Proof sketch: the map `ellipseAxisMap a b` carries the unit circle onto the ellipse whenever
-- `a, b ≠ 0`, and `ellipsePath a b` is that map applied to the standard unit circle
-- path.
theorem range_ellipsePath_eq_ellipse (a b : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) :
    Set.range (ellipsePath a b) =
      {z : ℂ | z.re ^ 2 / a ^ 2 + z.im ^ 2 / b ^ 2 = 1} := sorry

/- The parametrization `ellipseParam a b` traces exactly the same ellipse over the interval
`[0, 2π]` when `a` and `b` are nonzero. -/
-- Proof sketch: reparametrize the closed path `ellipsePath a b` by
-- `t = θ / (2π)` and use
-- `range_ellipsePath_eq_ellipse`; only nonvanishing of the semiaxes is needed for the set
-- equality.
theorem image_ellipseParam_eq_ellipse (a b : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) :
    ellipseParam a b '' Set.Icc (0 : ℝ) (2 * Real.pi) =
      {z : ℂ | z.re ^ 2 / a ^ 2 + z.im ^ 2 / b ^ 2 = 1} := sorry

/-- Integrating `dz / z` along the positively oriented ellipse gives `2π i`. -/
-- Proof sketch: `ellipsePath a b` is a positively oriented closed loop around the
-- origin when
-- `a, b > 0`; compute its contour integral from the winding index of the ellipse about `0`.
theorem curveIntegral_inv_ellipsePath_eq_two_pi_I (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    ∫ᶜ z in ellipsePath a b, indexForm 0 z =
      (2 * Real.pi * Complex.I : ℂ) := sorry

/-- Integrating the logarithmic derivative of the ellipse parametrization once around the ellipse
returns `2π i`. -/
-- Proof sketch: reparametrize the contour integral on `ellipsePath a b` by
-- `θ = 2π t`, then rewrite the integrand with mathlib's canonical `logDeriv`.
theorem integral_logDeriv_ellipseParam (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    ∫ t in (0 : ℝ)..(2 * Real.pi), logDeriv (ellipseParam a b) t =
      (2 * Real.pi * Complex.I : ℂ) := sorry

/-- Exercise 6: for positive semiaxes `a` and `b`, the standard ellipse parametrization yields
`∫_0^{2π} dt / (a^2 cos^2 t + b^2 sin^2 t) = 2π / (ab)`. -/
-- Proof sketch: expand `logDeriv (ellipseParam a b) t`, isolate its imaginary part as
-- `ab / (a^2 cos^2 t + b^2 sin^2 t)`, and compare the resulting integral with
-- `integral_logDeriv_ellipseParam`.
theorem ellipse_reciprocal_quadratic_integral_eq (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    ∫ t in (0 : ℝ)..(2 * Real.pi), 1 / (a ^ 2 * Real.cos t ^ 2 + b ^ 2 * Real.sin t ^ 2) =
      2 * Real.pi / (a * b) := sorry
