import Mathlib.Geometry.Manifold.Instances.Real
import Mathlib.Geometry.Manifold.ContMDiff.Basic
import Mathlib.Geometry.Manifold.MFDeriv.Basic

-- Declarations for this item will be appended below by the statement pipeline.

universe uM uH uE

noncomputable section

open scoped Manifold ContDiff

variable
  {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type uM} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

private abbrev unitTangentVector (t : ℝ) : TangentSpace 𝓘(ℝ) t := (1 : ℝ)

/-- Definition 3.17-extra-1: The velocity of a parametrized curve at a parameter value is the
manifold derivative of the curve applied to the unit tangent vector `d / dt` at that point. -/
abbrev curve_velocity (I : ModelWithCorners ℝ E H) (γ : ℝ → M) (t : ℝ) :
    TangentSpace I (γ t) :=
  mfderiv 𝓘(ℝ) I γ t (unitTangentVector t)

/-- The velocity of a parametrized curve at a parameter value, computed relative to a domain
subset of the parameter line. This is the one-sided/within-set variant used for boundary
arguments. -/
abbrev curve_velocityWithin (I : ModelWithCorners ℝ E H) (γ : ℝ → M) (s : Set ℝ) (t : ℝ) :
    TangentSpace I (γ t) :=
  mfderivWithin 𝓘(ℝ) I γ s t (unitTangentVector t)

omit [IsManifold I ∞ M] in
/-- On a parameter subset with unique differential and at a point where the curve is
manifold-differentiable, the within-set velocity agrees with the ordinary velocity. -/
theorem curve_velocityWithin_eq_curve_velocity {γ : ℝ → M} {s : Set ℝ} {t : ℝ}
    (hs : UniqueMDiffWithinAt 𝓘(ℝ) s t) (hγ : MDifferentiableAt 𝓘(ℝ) I γ t) :
    curve_velocityWithin I γ s t = curve_velocity I γ t := by
  simpa [curve_velocityWithin, curve_velocity] using
    DFunLike.congr_fun (mfderivWithin_eq_mfderiv hs hγ) (unitTangentVector t)
