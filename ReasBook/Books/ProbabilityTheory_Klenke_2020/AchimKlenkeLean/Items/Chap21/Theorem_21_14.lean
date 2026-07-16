import Mathlib
import ProbabilityTheory_Klenke_2020.AchimKlenkeLean.Items.Chap21.Definition_21_8

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory

universe u

namespace ProbabilityTheory

variable {Ω : Type u}

/-- The time-inversion transform of a real-valued process on `[0,∞)`. -/
noncomputable def timeInversion (B : NNReal → Ω → ℝ) : NNReal → Ω → ℝ :=
  fun t ω ↦ if t = 0 then 0 else (t : ℝ) * B (t⁻¹) ω

/-- The time-inverted process is given by the textbook piecewise formula. -/
theorem timeInversion_apply
    (B : NNReal → Ω → ℝ) (t : NNReal) (ω : Ω) :
    timeInversion B t ω = if t = 0 then 0 else (t : ℝ) * B (t⁻¹) ω :=
  rfl

namespace IsBrownianMotion

variable [MeasurableSpace Ω]

-- Proof sketch: view `timeInversion B` as a centered Gaussian process with covariance
-- kernel `s ⊓ t`, using the Brownian-motion characterization from Theorem 21.11. Continuity away
-- from `0` is immediate from continuity of `B`, and continuity at `0` follows from the large-time
-- asymptotics of `t⁻¹ • B t` together with the reflection-principle estimate from the textbook.
/-- Theorem 21.14: if `B` is a Brownian motion, then the process
`X_t = t B_{1 / t}` for `t > 0` and `X_0 = 0` is again a Brownian motion. -/
theorem timeInversion
    {μ : Measure Ω} {B : NNReal → Ω → ℝ} (hB : IsBrownianMotion μ B) :
    IsBrownianMotion μ (timeInversion B) := sorry

end IsBrownianMotion

end ProbabilityTheory
