import SmoothManifolds_Lee_2012.SmoothManifoldsLee.Chap03.Sec03_17.Corollary_3_25
import SmoothManifolds_Lee_2012.SmoothManifoldsLee.Chap05.Sec05_34.Notation_5_34_extra_1
import SmoothManifolds_Lee_2012.SmoothManifoldsLee.Chap05.Sec05_37.Problem_5_19

-- Declarations for this item will be appended below by the statement pipeline.

open scoped ContDiff Manifold

-- `lean_leansearch` was unavailable in this session, so this item follows the local figure-eight
-- counterexample infrastructure already formalized in `Problem_5_19`.

/-- Problem 5-20 (1): for the immersed figure-eight in `ℝ²`, every smooth function on the ambient
plane that vanishes on the image has zero differential at the self-intersection along the velocity
vector of the branch through parameter `0`. -/
theorem figureEightCurveMap_branch_velocity_annihilates_vanishing_functions
    (f : C^∞⟮𝓘(ℝ, ℝ × ℝ), ℝ × ℝ; ℝ⟯)
    (hzero : Set.EqOn f 0 (Set.range figureEightCurveMap)) :
    mfderiv 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ) f (figureEightCurveMap 0)
      (curve_velocity 𝓘(ℝ, ℝ × ℝ) figureEightCurveMap 0) = 0 :=
  by
  have hcomp_zero : f ∘ figureEightCurveMap = fun _ : ℝ ↦ (0 : ℝ) := by
    funext t
    exact hzero ⟨t, rfl⟩
  have hf_contDiffAt : ContDiffAt ℝ ∞ f (figureEightCurveMap 0) := by
    simpa using (f.contMDiff (figureEightCurveMap 0)).contDiffAt
  have hf_diff : DifferentiableAt ℝ f (figureEightCurveMap 0) := by
    exact hf_contDiffAt.differentiableAt (show (∞ : WithTop ℕ∞) ≠ 0 by simp)
  have hcomp_deriv :
      deriv (f ∘ figureEightCurveMap) 0 =
        fderiv ℝ f (figureEightCurveMap 0) (deriv figureEightCurveMap 0) := by
    simpa using
      fderiv_comp_deriv 0 hf_diff (figureEightCurveMap_hasDerivAt 0).differentiableAt
  have hcurve_velocity :
      curve_velocity 𝓘(ℝ, ℝ × ℝ) figureEightCurveMap 0 = deriv figureEightCurveMap 0 := by
    rw [curve_velocity, mfderiv_eq_fderiv]
    rfl
  have hconst_deriv : deriv (f ∘ figureEightCurveMap) 0 = 0 := by
    simp [hcomp_zero]
  have hgoal :
      fderiv ℝ f (figureEightCurveMap 0)
        (curve_velocity 𝓘(ℝ, ℝ × ℝ) figureEightCurveMap 0) = 0 := by
    rw [hcurve_velocity]
    exact hcomp_deriv.symm.trans hconst_deriv
  simpa [mfderiv_eq_fderiv] using hgoal

/-- Problem 5-20 (2): at the same ambient self-intersection point of the immersed figure-eight,
the velocity vector of the branch through parameter `0` is not tangent to the other branch
through parameter `π`, after identifying tangent spaces of `ℝ²` with `ℝ²`. -/
theorem figureEightCurveMap_branch_velocity_not_tangent_to_other_branch :
    figureEightBranchVelocity 0 ∉ figureEightTangentLine Real.pi :=
  figureEightCurveMap_counterexample.2
