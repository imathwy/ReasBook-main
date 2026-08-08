import Mathlib
import ProbabilityTheory_Klenke_2020.Chap09.Definition_9_7
import ProbabilityTheory_Klenke_2020.Chap21.Definition_21_4
import ProbabilityTheory_Klenke_2020.Chap21.Definition_21_8
import ProbabilityTheory_Klenke_2020.Chap21.Exercise_21_2_2
import ProbabilityTheory_Klenke_2020.Chap25.Theorem_25_18

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory

noncomputable section

universe u

/- Example 25.20 uses the canonical Chapter 21 notion
`ProbabilityTheory.HasAlmostSurelyContinuousPaths`. -/
recall ProbabilityTheory.HasAlmostSurelyContinuousPaths

/- The defining equivalence for almost-sure path continuity is the existing theorem
`ProbabilityTheory.hasAlmostSurelyContinuousPaths_iff`. -/
recall ProbabilityTheory.hasAlmostSurelyContinuousPaths_iff

/- Example 25.20 uses the canonical Chapter 9 notion
`IsSquareIntegrableProcess`. -/
recall IsSquareIntegrableProcess

/- The defining `L²` characterization is the existing theorem
`isSquareIntegrableProcess_iff`. -/
recall isSquareIntegrableProcess_iff

/- The Brownian-motion hypothesis in this file is the canonical Chapter 21 class
`ProbabilityTheory.IsBrownianMotion`. -/
recall ProbabilityTheory.IsBrownianMotion

/- Example 25.20 (2) extends the existing Brownian compensated-square martingale theorem
`ProbabilityTheory.brownian_sq_sub_time_martingale` by adding the path-continuity conclusion. -/
recall ProbabilityTheory.brownian_sq_sub_time_martingale

/- The compensator `t ↦ ∫_0^t H_s^2 ds` used below is the canonical Chapter 25 process
`MeasureTheory.secondMomentCompensator`. -/
recall MeasureTheory.secondMomentCompensator

/- The canonical compensated-square construction is
`MeasureTheory.brownianItoCompensatedSquareProcess`. -/
recall MeasureTheory.brownianItoCompensatedSquareProcess

namespace ProbabilityTheory

variable {Ω : Type u}

local notation "Process" => NNReal → Ω → ℝ

variable [MeasurableSpace Ω]

section

variable {μ : Measure Ω} {W : Process} (hW : IsBrownianMotion μ W)

local notation "ℱW" => Filtration.natural W hW.stronglyMeasurable
local notation "BrownianSqSubTime" => fun t ω ↦ W t ω ^ 2 - (t : ℝ)
local notation "BrownianSelfIntegral" => fun t ω ↦ BrownianSqSubTime t ω / 2

-- Proof sketch: use independent centered Brownian increments to prove the martingale property for
-- the natural filtration, and use the Gaussian marginal law at each fixed time to obtain the `L²`
-- condition.
/-- Example 25.20 (1): the Brownian motion itself, viewed as `W_t = ∫_0^t 1 dW_s`, is a
square-integrable martingale for its natural filtration. -/
theorem brownian_isSquareIntegrable_martingale
    : Martingale W ℱW μ ∧
      IsSquareIntegrableProcess W μ := sorry

-- Proof sketch: combine the existing compensated-square martingale theorem for Brownian motion
-- with almost-sure continuity of Brownian paths; squaring and subtracting the deterministic path
-- `t ↦ t` preserve continuity.
/-- Example 25.20 (2): the compensated square process `(W_t^2 - t)_{t ≥ 0}` is a continuous
martingale for the natural filtration of Brownian motion. -/
theorem brownian_sq_sub_time_continuous_martingale
    : Martingale BrownianSqSubTime ℱW μ ∧
      HasAlmostSurelyContinuousPaths μ BrownianSqSubTime := sorry

-- Proof sketch: identify `t ↦ (W_t^2 - t) / 2` with one half of the compensated-square martingale
-- from part (2); scalar multiplication preserves the martingale property and the `L²` condition.
/-- Example 25.20 (3): the process `M_t = ∫_0^t W_s dW_s`, represented by
`t ↦ (W_t^2 - t) / 2`, is a square-integrable martingale. -/
theorem brownianSelfIntegral_isSquareIntegrable_martingale
    : Martingale BrownianSelfIntegral ℱW μ ∧
      IsSquareIntegrableProcess BrownianSelfIntegral μ := sorry

-- Proof sketch: almost-sure continuity of Brownian paths implies continuity of
-- `t ↦ (W_t^2 - t) / 2` by composition with continuous algebraic operations.
/-- Example 25.20 (4): the Brownian self-integral process `M_t = ∫_0^t W_s dW_s` has almost
surely continuous sample paths. -/
theorem brownianSelfIntegral_hasAlmostSurelyContinuousPaths
    : HasAlmostSurelyContinuousPaths μ BrownianSelfIntegral := sorry

-- Proof sketch: apply Itô's formula in the form `d(M_t^2) = 2 M_t dM_t + W_t^2 dt` to the
-- Brownian self-integral `M_t = ∫_0^t W_s dW_s`; the stochastic term is again a martingale, and
-- continuity follows from the continuity of `M` and of the time integral of `W_s^2`.
/-- Example 25.20 (5): the compensated square of the Brownian self-integral,
`((∫_0^t W_s dW_s)^2 - ∫_0^t W_s^2 ds)_{t ≥ 0}`, is a continuous martingale. -/
theorem brownianSelfIntegral_compensatedSquare_continuous_martingale
    : Martingale (brownianItoCompensatedSquareProcess BrownianSelfIntegral W) ℱW μ ∧
      HasAlmostSurelyContinuousPaths μ
        (brownianItoCompensatedSquareProcess BrownianSelfIntegral W) := sorry

end

end ProbabilityTheory
