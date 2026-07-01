import Mathlib
import AchimKlenkeLean.Items.Chap21.Theorem_21_14
import AchimKlenkeLean.Items.Chap22.Theorem_22_1

-- Declarations for this item will be appended below by the statement pipeline.

open Filter MeasureTheory
open scoped NNReal Topology

universe u

namespace ProbabilityTheory

variable {Ω : Type u} [MeasurableSpace Ω]

namespace IsBrownianMotion

/- Corollary 22.3 is `source-facing`: it records the local law of the iterated logarithm for the
increment process at a fixed time. Its core/canonical owner remains `IsBrownianMotion`; the
primitive data are a Brownian motion `B` and a time `s`, while the local limsup formula is derived
from the owner-level time-inversion theorem and the global law of the iterated logarithm. -/

-- Proof sketch: for fixed `s`, the increment process `t ↦ B (s + t) - B s` is again a Brownian
-- motion by stationary independent increments and almost-sure continuity. Apply Theorem 22.1 to
-- the time inversion from Theorem 21.14 of that increment process, equivalently to
-- `t ↦ t * (B (s + t⁻¹) - B s)`, and rewrite the resulting asymptotic statement back as the
-- one-sided `t ↓ 0` limsup of the normalized increment process.
/-- Corollary 22.3: for every `s ≥ 0`, Brownian increments at time `s` satisfy the local law of
the iterated logarithm
`limsup_{t ↓ 0} (B (s + t) - B s) / sqrt(2 t log log (1 / t)) = 1` almost surely. -/
theorem ae_limsup_increment_div_sqrt_two_mul_t_log_log_inv_eq_one
    {μ : Measure Ω} {B : NNReal → Ω → ℝ} (hB : IsBrownianMotion μ B) (s : NNReal) :
    ∀ᵐ ω ∂μ,
      limsup
        (fun t : NNReal ↦
          (B (s + t) ω - B s ω) /
            Real.sqrt (2 * (t : ℝ) * Real.log (Real.log ((t : ℝ)⁻¹))))
        (𝓝[>] (0 : NNReal)) = 1 := sorry

end IsBrownianMotion

end ProbabilityTheory
