import Mathlib
import AchimKlenkeLean.Items.Chap21.Theorem_21_70
import AchimKlenkeLean.Items.Chap25.Theorem_25_17

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory
open scoped ENNReal

noncomputable section

namespace MeasureTheory

universe u

variable {Ω : Type u} [MeasurableSpace Ω]

local notation "ContinuousFiltration" => Filtration NNReal (inferInstance : MeasurableSpace Ω)
local notation "Process" => NNReal → Ω → ℝ

/-- The compensator `t ↦ ∫_0^t H_s^2 ds` attached to a real-valued process `H`. -/
noncomputable def secondMomentCompensator (H : Process) : Process :=
  fun t ω ↦
    ∫ s in Set.Icc (0 : ℝ) (t : ℝ), (H (Real.toNNReal s) ω) ^ 2 ∂(volume : Measure ℝ)

-- Proof sketch: unfold `secondMomentCompensator`; by definition it is the time integral of the
-- squared process over the interval `[0, t]`.
omit [MeasurableSpace Ω] in
/-- Evaluating `secondMomentCompensator H` at time `t` gives the time integral of `H^2` over
`[0, t]`. -/
theorem secondMomentCompensator_apply (H : Process) (t : NNReal) (ω : Ω) :
    secondMomentCompensator H t ω =
      ∫ s in Set.Icc (0 : ℝ) (t : ℝ), (H (Real.toNNReal s) ω) ^ 2 ∂(volume : Measure ℝ) := rfl

/-- The compensated square process `M_t^2 - ∫_0^t H_s^2 ds` attached to the abstract Brownian Itô
integral process `I_t = ∫_0^t H_s dW_s`. -/
noncomputable def brownianItoCompensatedSquareProcess
    (I H : Process) : Process :=
  fun t ω ↦ (I t ω) ^ 2 - secondMomentCompensator H t ω

-- Proof sketch: unfold `brownianItoCompensatedSquareProcess`; the process is defined pointwise by
-- subtracting the square compensator from the squared integral process.
omit [MeasurableSpace Ω] in
/-- Evaluating the compensated square process gives `M_t^2 - ∫_0^t H_s^2 ds`. -/
theorem brownianItoCompensatedSquareProcess_apply
    (I H : Process) (t : NNReal) (ω : Ω) :
    brownianItoCompensatedSquareProcess I H t ω =
      (I t ω) ^ 2 - secondMomentCompensator H t ω := rfl

variable {ℱ : ContinuousFiltration} {μ : Measure Ω}
variable {H I : Process}

/-
Theorem 25.18 (1): for a progressively measurable integrand whose squared time integral has
finite expectation on every deterministic compact interval `[0,T]` with `T > 0`, the Brownian
Itô integral process is a square-integrable continuous martingale.

This is exactly the canonical theorem
`ProbabilityTheory.localBrownianIntegral_isSquareIntegrableContinuousMartingale`.
-/
recall ProbabilityTheory.localBrownianIntegral_isSquareIntegrableContinuousMartingale

-- Proof sketch: apply Itô's formula to `x ↦ x^2` for the Brownian Itô integral process. The
-- finite-variation term is `∫_0^t H_s^2 ds`, so subtracting it leaves a martingale; continuity is
-- inherited from the continuous paths of the integral process and the time integral.
/-- Theorem 25.18 (2): the explicit compensated square process
`N_t = (∫_0^t H_s dW_s)^2 - ∫_0^t H_s^2 ds` is a continuous martingale with `N_0 = 0`. -/
theorem brownianItoIntegral_compensatedSquare_isContinuousMartingale
    [IsProbabilityMeasure μ]
    {W : Process}
    (_hI : ProbabilityTheory.IsBrownianLocalItoIntegral ℱ μ W H I)
    (_hH_second : ∀ T : NNReal, 0 < T → HasFiniteStoppedSecondMoment μ H fun _ ↦ (T : ENNReal)) :
    Martingale (brownianItoCompensatedSquareProcess I H) ℱ μ ∧
      HasAlmostSurelyContinuousPaths μ
        (brownianItoCompensatedSquareProcess I H) ∧
      brownianItoCompensatedSquareProcess I H 0 = 0 := sorry

/-- The compensator `t ↦ ∫_0^t H_s^2 ds` realizes the canonical continuous square variation of the
Brownian Itô integral process. This is the thin library-facing bridge from the explicit
compensated-square martingale statement in Theorem 25.18 (2) to
`IsContinuousSquareVariationProcess`. -/
theorem brownianItoIntegral_hasContinuousSquareVariation
    [IsProbabilityMeasure μ]
    {W : Process}
    (_hI : ProbabilityTheory.IsBrownianLocalItoIntegral ℱ μ W H I)
    (_hH_second : ∀ T : NNReal, 0 < T → HasFiniteStoppedSecondMoment μ H fun _ ↦ (T : ENNReal)) :
    IsContinuousSquareVariationProcess ℱ μ
      I (secondMomentCompensator H) := sorry

end MeasureTheory
