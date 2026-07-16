import Mathlib
import ProbabilityTheory_Klenke_2020.AchimKlenkeLean.Items.Chap21.Definition_21_8

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory

universe u

namespace ProbabilityTheory

variable {Ω : Type u} [MeasurableSpace Ω]

-- Proof sketch: for `s ≤ t`, split the exponent into the time-`s` part and the increment
-- `B_t - B_s`. Brownian independent increments imply that this increment is independent of the
-- natural filtration up to time `s`, while its centered Gaussian law gives expectation
-- `exp ((σ^2 / 2) * (t - s))`. This exactly cancels the compensator, yielding the martingale
-- conditional-expectation identity.
/-- Exercise 21.2.3: for a Brownian motion `B`, the process
`t ↦ exp (σ B_t - (σ^2 / 2) t)` is a martingale with respect to the natural filtration generated
by `B`. -/
theorem brownianStochasticExponential_martingale
    {μ : Measure Ω} {B : NNReal → Ω → ℝ} (hB : IsBrownianMotion μ B) (σ : ℝ) :
    Martingale
      (fun t ω ↦ Real.exp (σ * B t ω - (σ ^ 2 / 2) * (t : ℝ)))
      (Filtration.natural B hB.stronglyMeasurable)
      μ := sorry

end ProbabilityTheory
