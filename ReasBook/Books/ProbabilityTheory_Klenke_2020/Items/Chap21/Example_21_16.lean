import Mathlib
import ProbabilityTheory_Klenke_2020.Items.Chap21.Definition_21_8
import ProbabilityTheory_Klenke_2020.Items.Chap21.Exercise_21_4_4

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory

noncomputable section

universe u

namespace ProbabilityTheory

variable {Ω : Type u} [MeasurableSpace Ω]

private def sqrtBoundaryGapProcess (B : NNReal → Ω → ℝ) (K : ℝ) : NNReal → Ω → ℝ :=
  fun t ω ↦ B t ω - K * Real.sqrt (t : ℝ)

-- Proof sketch: combine the Brownian scaling property with Blumenthal's zero-one law for the
-- right-limit sigma-algebra `𝓕⁺ 0`. Apply this to the upper-boundary event for the gap process
-- `t ↦ B t - K * sqrt t`; scaling identifies the event of entering `[0, ∞)` in an arbitrarily
-- small positive interval with a positive-probability Brownian event, and the zero-one law then
-- upgrades this to an almost-sure statement.
/-- Example 21.16: for Brownian motion `B` and every `K`, the first strictly positive time at
which `B t ≥ K * sqrt t` is almost surely equal to `0`. Equivalently,
`inf {t > 0 : K * sqrt t ≤ B t} = 0` almost surely. -/
theorem brownianSqrtBoundaryHittingTime_ae_eq_zero
    {μ : Measure Ω} {B : NNReal → Ω → ℝ} (hB : IsBrownianMotion μ B) (K : ℝ) :
    ∀ᵐ ω ∂μ,
      (τ_[(sqrtBoundaryGapProcess B K), Set.Ici (0 : ℝ)]) ω = 0 := sorry

end ProbabilityTheory
