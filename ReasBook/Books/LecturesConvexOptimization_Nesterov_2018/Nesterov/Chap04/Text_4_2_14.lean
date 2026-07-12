import LecturesConvexOptimization_Nesterov_2018.Chap04.Algorithm_4_2_5
import LecturesConvexOptimization_Nesterov_2018.Chap04.Definition_4_2_12

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

open scoped ConstrainedArgmin
open ModifiedAcceleratedCubicNewton

/- Text 4.2.14 lies in the Chapter 4 modified accelerated cubic-Newton step domain.

Sampled owner-style declarations:
* `argmin[{xk, step yk}] f` in `Algorithm_4_2_5`, the canonical accepted-point owner for
  `x̂_k`;
* `ModifiedAcceleratedCubicNewton.isMinOn` in `Algorithm_4_2_5`, the canonical source of the
  comparison `f x̂_k ≤ f x_k`;
* `ModifiedAcceleratedCubicNewton.xNext` in `Algorithm_4_2_5`, the owner-derived next
  iterate `x_{k+1}`;
* `CubicRegularizationMapping` in `Definition_4_2_12`, the canonical owner of the cubic trial
  map `T_{2L₃}` used by the modified step.

Best owner abstraction:
* source-facing: the present item is a one-step objective-gap estimate;
* core/canonical: the accepted-point subtype `argmin[{xk, step yk}] f` together with
  `IsMinOn f Set.univ xStar`;
* bridge/view: the cubic decrease and step-length inequalities evaluated at the owner-derived
  points `xHat` and `xNext xHat`.

Primitive data:
* the objective `f`;
* the chapter-standard constant `L3 : NNReal`;
* the cubic step owner `step : CubicRegularizationMapping f (2 * (L3 : ℝ))`;
* the canonical accepted-point owner `xHat : argmin[{xk, step yk}] f`;
* the minimizer `xStar`;
* the strong-convexity scalar `σ₂`;
* the cubic decrease and step-length lower bounds for `xHat` and `xNext xHat`.

Derived API:
* the accepted-point comparison `f xHat ≤ f xk`, obtained canonically from `isMinOn xHat`;
* the first displayed drop comparison;
* the square-root next-gap lower bound.

The previous version duplicated the Chapter 4 owner layer by carrying raw sequences `x` and
`hatX` and by storing `f (x k) ≥ f (hatX k)` as primitive data, even though Algorithm 4.2.5
already records `x̂_k` through the canonical two-point `argmin` owner. This refinement keeps the
source-facing theorem but rewrites it directly on that canonical binder, so the accepted-point
comparison is derived from the owner abstraction instead of repeated as a parallel
hypothesis. It also restores the chapter-standard `L3 : NNReal` surface. -/

-- Proof sketch: apply `ModifiedAcceleratedCubicNewton.isMinOn xHat` to the competitor `xk` to
-- get `f xHat ≤ f xk`, then subtract the common term `f (xNext xHat)`.
/-- The accepted-point owner from Algorithm 4.2.5 immediately gives the comparison
`f x_k - f x_{k+1} ≥ f xHat - f x_{k+1}`. This is the bridge/view part of Text 4.2.14. -/
theorem modified_accelerated_cubic_drop_ge_hat_drop
    (f : E → ℝ) (L3 : NNReal) {xk yk : E}
    (step : CubicRegularizationMapping f (2 * (L3 : ℝ)))
    (xHat : argmin[{xk, step yk}] f) :
    f xk - f (xNext xHat) ≥ f xHat - f (xNext xHat) := by
  have hxHat_le_xk : f xHat ≤ f xk := by
    simpa using
      (ModifiedAcceleratedCubicNewton.isMinOn xHat)
        (by simp : xk ∈ ({xk, step yk} : Set E))
  linarith

-- Proof sketch: combine the assumed cubic decrease estimate with the step-length lower bound and
-- simplify the constants.
/-- Text 4.2.14: let `xHat : argmin[{xk, step yk}] f` be the accepted point `x̂_k` chosen by
Algorithm 4.2.5 for the cubic owner `step : CubicRegularizationMapping f (2 L₃)`, and let
`xNext xHat` be the next iterate `x_{k+1}`. If `xStar` is a global minimizer of `f`,
`σ₂ > 0`, and the step satisfies
`f xHat - f (xNext xHat) ≥ (σ₂ / 6) ‖xNext xHat - xHat‖^3` together with
`‖xNext xHat - xHat‖ ≥
  (sqrt 2 * σ₂^(1/6) / L₃^(1/3))
  (f (xNext xHat) - f xStar)^(1/6)`,
then
`f xHat - f x_{k+1} ≥ (sqrt 2 * σ₂^(3/2) / (3 L₃)) (f x_{k+1} - f xStar)^(1/2)`. -/
theorem modified_accelerated_cubic_hat_drop_ge_sqrt_next_gap
    (f : E → ℝ) (L3 : NNReal) {xk yk : E}
    (step : CubicRegularizationMapping f (2 * (L3 : ℝ)))
    (xHat : argmin[{xk, step yk}] f)
    (xStar : E) (σ₂ : ℝ)
    (hxStar : IsMinOn f Set.univ xStar)
    (hσ₂ : 0 < σ₂)
    (hcubic :
      f xHat - f (xNext xHat) ≥
        (σ₂ / 6 : ℝ) * ‖xNext xHat - xHat‖ ^ (3 : ℕ))
    (hstep :
      ‖xNext xHat - xHat‖ ≥
        ((Real.sqrt 2 * Real.rpow σ₂ (1 / 6 : ℝ)) /
            Real.rpow (L3 : ℝ) (1 / 3 : ℝ)) *
          Real.rpow (f (xNext xHat) - f xStar) (1 / 6 : ℝ)) :
    f xHat - f (xNext xHat) ≥
      ((Real.sqrt 2 * Real.rpow σ₂ (3 / 2 : ℝ)) / (3 * (L3 : ℝ))) *
        Real.sqrt (f (xNext xHat) - f xStar) := sorry

end
