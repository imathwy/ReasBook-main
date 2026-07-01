import Mathlib
import Nesterov.Chap07.Algorithm_7_2
import Nesterov.Chap07.Definition_7_1
import Nesterov.Chap07.Theorem_7_2

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

section

variable {X : Type u}

/- Theorem 7.3 lies in the autonomous discrete-trajectory / first-stopping-time domain.

Sampled owner-style declarations:
- `relativeScaleSubgradientApproximationIterate`,
  `relativeScaleSubgradientApproximationStoppingIndex`, and
  `relativeScaleSubgradientApproximationStoppingTime` in `Algorithm_7_2.lean`;
- `ConstrainedLevelMethod.stoppingIndex` in `Chap03/Algorithm_3_11.lean`;
- `gradientMethod` in `Chap01/Algorithm_1_6_1.lean`;
- `NewtonSystem.orbit` in `Chap01/Algorithm_1_7_1.lean`.

Best owner abstraction:
- source-facing: Theorem 7.3's stopping-time, terminal-value, and work bounds for Algorithm 7.2;
- core/canonical: the Algorithm 7.2 iterate owner
  `relativeScaleSubgradientApproximationIterate G f x0 δ α γ0` together with the canonical
  stopping index/time derived from `hTerminate`;
- bridge/view: the derived lower-level work count
  `relativeScaleSubgradientApproximationTotalLowerLevelSteps hTerminate`.

Primitive data:
- the update-scheme data `G`, `f`, `x0`, `δ`, `α`, and `γ0`;
- the existence witness `hTerminate` for the stopping criterion;
- the actual optimality data and Chapter 7 parameter relations;
- the lower-level stage guarantee attached to the fixed block length.

Derived API:
- the canonical stage sequence `\hat x_t`;
- the first stopping index `s` and stopping time `T = s + 1`;
- the total lower-level work up to `T`;
- the three bounds asserted by Theorem 7.3.

Source/core/bridge triage:
- source-facing: the three theorem conclusions;
- core/canonical: the Algorithm 7.2 iterate and stopping-time owners;
- bridge/view: the work-count formula `T * (\hat N + 1)`.

The stopping data already has a canonical owner in `Algorithm_7_2.lean`, so this file states the
Theorem 7.3 conclusions directly on that owner instead of introducing a separate public result
wrapper.
-/

/-- The total number of lower-level gradient steps used by the relative-scale subgradient
approximation trajectory up to its stopping time, assuming that each stage uses
`relativeScaleSubgradientApproximationBlockLength δ α + 1` lower-level steps. -/
def relativeScaleSubgradientApproximationTotalLowerLevelSteps
    {f : X → ℝ} {G : ℕ → ℝ → X} {x0 : X} {δ α γ0 : ℝ}
    (hTerminate : relativeScaleSubgradientApproximationTerminates G f x0 δ α γ0) : ℕ :=
  relativeScaleSubgradientApproximationStoppingTime hTerminate *
    (relativeScaleSubgradientApproximationBlockLength δ α + 1)

-- Proof sketch: unfold `relativeScaleSubgradientApproximationTotalLowerLevelSteps`.
/-- Expanding `relativeScaleSubgradientApproximationTotalLowerLevelSteps` gives the product of the
stopping time and the per-stage lower-level step count. -/
theorem relativeScaleSubgradientApproximationTotalLowerLevelSteps_def
    {f : X → ℝ} {G : ℕ → ℝ → X} {x0 : X} {δ α γ0 : ℝ}
    (hTerminate : relativeScaleSubgradientApproximationTerminates G f x0 δ α γ0) :
    relativeScaleSubgradientApproximationTotalLowerLevelSteps hTerminate =
      relativeScaleSubgradientApproximationStoppingTime hTerminate *
        (relativeScaleSubgradientApproximationBlockLength δ α + 1) :=
  rfl

section TerminationBounds

variable [NormedAddCommGroup X]
variable {f : X → ℝ} {G : ℕ → ℝ → X} {x0 xStar : X} {δ α γ0 γ1 : ℝ}

local notation "x̂" => relativeScaleSubgradientApproximationIterate G f x0 δ α γ0

variable
  (hTerminate : relativeScaleSubgradientApproximationTerminates G f x0 δ α γ0)

local notation "T" => relativeScaleSubgradientApproximationStoppingTime hTerminate

-- Proof sketch: use `relativeScaleSubgradientApproximationStoppingIndex_min` to show that before
-- the first accepted stage the objective decays by the factor `1 / √e`, then combine the
-- resulting estimate at `T - 1` with the optimality witness `hxStar` and the lower bound
-- `α * f x0 ≤ f xStar` to obtain `(T : ℝ) ≤ 1 + 2 log (1 / α)`. For the terminal value, apply the
-- lower-level stage guarantee at time `T - 1`, use the distance bound
-- `‖x0 - xStar‖ ≤ aPrioriRadiusEstimate f γ0 xStar`, rewrite the chapter parameter relation as
-- `α = γ0 / γ1`, and derive the required coefficient estimate from the canonical block-length
-- formula in `relativeScaleSubgradientApproximationBlockLength`. Finally multiply the per-stage
-- block length by the stopping-time bound to control the total lower-level work.
/-- Theorem 7.3 (1): under the canonical stopping-time setup for Algorithm 7.2, the stopping time
`T` is bounded above by `1 + 2 log (1 / α)`. -/
theorem relativeScaleSubgradientApproximation_stopping_time_bound
    (hα : 0 < α)
    (hδ : 0 < δ)
    (hInitialValue_pos : 0 < f x0)
    (hxStar : IsMinOn f Set.univ xStar)
    (hOptimalValue_lower : α * f x0 ≤ f xStar)
    (hOptimal_solution_distance : ‖x0 - xStar‖ ≤ aPrioriRadiusEstimate f γ0 xStar)
    (hParameter_relation : α = γ0 / γ1)
    (hLowerLevel_gap :
      ∀ t : ℕ,
        f (x̂ (t + 1)) - f xStar ≤
          (γ1 / Real.sqrt ((relativeScaleSubgradientApproximationBlockLength δ α : ℝ) + 1)) *
            ‖x0 - xStar‖)
    : (T : ℝ) ≤ 1 + 2 * Real.log (1 / α) := sorry

-- Proof sketch: apply the lower-level stage guarantee at time `T - 1`, use the distance bound
-- `‖x0 - xStar‖ ≤ aPrioriRadiusEstimate f γ0 xStar`, rewrite `α = γ0 / γ1`, and compare the
-- resulting terminal estimate with the minimizer value `f xStar`.
/-- Theorem 7.3 (2): under the canonical stopping-time setup for Algorithm 7.2, the terminal value
`f(\hat x_T)` has relative accuracy `δ` with respect to `f(xStar)`. -/
theorem relativeScaleSubgradientApproximation_terminal_relative_accuracy
    (hα : 0 < α)
    (hδ : 0 < δ)
    (hInitialValue_pos : 0 < f x0)
    (hxStar : IsMinOn f Set.univ xStar)
    (hOptimalValue_lower : α * f x0 ≤ f xStar)
    (hOptimal_solution_distance : ‖x0 - xStar‖ ≤ aPrioriRadiusEstimate f γ0 xStar)
    (hParameter_relation : α = γ0 / γ1)
    (hLowerLevel_gap :
      ∀ t : ℕ,
        f (x̂ (t + 1)) - f xStar ≤
          (γ1 / Real.sqrt ((relativeScaleSubgradientApproximationBlockLength δ α : ℝ) + 1)) *
            ‖x0 - xStar‖)
    : IsRelativeAccuracy (f xStar) δ (f (x̂ T)) := sorry

-- Proof sketch: combine the stopping-time bound from Theorem 7.3 (1) with the explicit formula
-- for `relativeScaleSubgradientApproximationTotalLowerLevelSteps`, using that each stage performs
-- `relativeScaleSubgradientApproximationBlockLength δ α + 1` lower-level steps.
/-- Theorem 7.3 (3): under the canonical stopping-time setup for Algorithm 7.2, the total number
of lower-level gradient steps up to time `T` is bounded by
`(e / α²) (1 + 1 / δ)² (1 + 2 log (1 / α))`. -/
theorem relativeScaleSubgradientApproximation_total_lower_level_steps_bound
    (hα : 0 < α)
    (hδ : 0 < δ)
    (hInitialValue_pos : 0 < f x0)
    (hxStar : IsMinOn f Set.univ xStar)
    (hOptimalValue_lower : α * f x0 ≤ f xStar)
    (hOptimal_solution_distance : ‖x0 - xStar‖ ≤ aPrioriRadiusEstimate f γ0 xStar)
    (hParameter_relation : α = γ0 / γ1)
    (hLowerLevel_gap :
      ∀ t : ℕ,
        f (x̂ (t + 1)) - f xStar ≤
          (γ1 / Real.sqrt ((relativeScaleSubgradientApproximationBlockLength δ α : ℝ) + 1)) *
            ‖x0 - xStar‖)
    :
    (relativeScaleSubgradientApproximationTotalLowerLevelSteps hTerminate : ℝ) ≤
      ((Real.exp 1) / (α ^ (2 : ℕ))) * (1 + 1 / δ) ^ (2 : ℕ) *
        (1 + 2 * Real.log (1 / α)) := sorry

end TerminationBounds

end
