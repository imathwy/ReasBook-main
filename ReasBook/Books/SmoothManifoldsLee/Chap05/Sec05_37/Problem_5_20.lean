import SmoothManifoldsLee.Chap03.Sec03_17.Corollary_3_25
import SmoothManifoldsLee.Chap05.Sec05_34.Notation_5_34_extra_1
import SmoothManifoldsLee.Chap05.Sec05_37.Problem_5_19

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
    mfderiv% f (figureEightCurveMap 0)
      (curve_velocity 𝓘(ℝ, ℝ × ℝ) figureEightCurveMap 0) = 0 :=
  by
  have hcomp_zero : f ∘ figureEightCurveMap = fun _ : ℝ ↦ 0 := by
    funext t
    exact hzero ⟨t, rfl⟩
  have hfigureEight :
      ContMDiffOn 𝓘(ℝ) 𝓘(ℝ, ℝ × ℝ) (∞ : ℕ∞ω) figureEightCurveMap Set.univ := by
    simpa using figureEightCurveMap_contDiff.contMDiff.contMDiffOn
  have hfigureEight_diff :
      MDifferentiableAt 𝓘(ℝ) 𝓘(ℝ, ℝ × ℝ) figureEightCurveMap 0 := by
    simpa using figureEightCurveMap_contDiff.contMDiff.mdifferentiableAt
      (show (∞ : ℕ∞ω) ≠ 0 by simp)
  have hfigureEight_velocity :
      curve_velocityWithin 𝓘(ℝ, ℝ × ℝ) figureEightCurveMap Set.univ 0 =
        curve_velocity 𝓘(ℝ, ℝ × ℝ) figureEightCurveMap 0 := by
    exact curve_velocityWithin_eq_curve_velocity
      (uniqueMDiffWithinAt_univ 𝓘(ℝ)) hfigureEight_diff
  have hzero_velocity :
      curve_velocityWithin 𝓘(ℝ) (fun _ : ℝ ↦ (0 : ℝ)) Set.univ 0 =
        curve_velocity 𝓘(ℝ) (fun _ : ℝ ↦ (0 : ℝ)) 0 := by
    exact curve_velocityWithin_eq_curve_velocity
      (uniqueMDiffWithinAt_univ 𝓘(ℝ))
      (by
        simpa using
          (contMDiff_const :
            ContMDiff 𝓘(ℝ) 𝓘(ℝ) (∞ : ℕ∞ω) (fun _ : ℝ ↦ (0 : ℝ))).mdifferentiableAt
            (show (∞ : ℕ∞ω) ≠ 0 by simp))
  have hcomp_velocity :
      mfderiv% f (figureEightCurveMap 0)
          (curve_velocity 𝓘(ℝ, ℝ × ℝ) figureEightCurveMap 0) =
        curve_velocity 𝓘(ℝ) (f ∘ figureEightCurveMap) 0 := by
    calc
      mfderiv% f (figureEightCurveMap 0)
          (curve_velocity 𝓘(ℝ, ℝ × ℝ) figureEightCurveMap 0)
        = curve_velocityWithin 𝓘(ℝ) (f ∘ figureEightCurveMap) Set.univ 0 := by
            exact differential_eq_velocity_of_composite_curve
              (by simp)
              (uniqueMDiffWithinAt_univ 𝓘(ℝ)) f.contMDiff hfigureEight rfl hfigureEight_velocity
      _ = curve_velocity 𝓘(ℝ) (f ∘ figureEightCurveMap) 0 := by
            rw [hcomp_zero]
            exact hzero_velocity
  calc
    mfderiv% f (figureEightCurveMap 0)
        (curve_velocity 𝓘(ℝ, ℝ × ℝ) figureEightCurveMap 0)
      = curve_velocity 𝓘(ℝ) (f ∘ figureEightCurveMap) 0 := hcomp_velocity
    _ = curve_velocity 𝓘(ℝ) (fun _ : ℝ ↦ 0) 0 := by simp [hcomp_zero]
    _ = 0 := by simp [curve_velocity]

/-- Problem 5-20 (2): at the same ambient self-intersection point of the immersed figure-eight,
the velocity vector of the branch through parameter `0` is not tangent to the other branch
through parameter `π`, after identifying tangent spaces of `ℝ²` with `ℝ²`. -/
theorem figureEightCurveMap_branch_velocity_not_tangent_to_other_branch :
    figureEightBranchVelocity 0 ∉ figureEightTangentLine Real.pi :=
  figureEightCurveMap_counterexample.2
