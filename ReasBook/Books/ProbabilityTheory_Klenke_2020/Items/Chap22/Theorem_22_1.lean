import Mathlib
import ProbabilityTheory_Klenke_2020.Items.Chap21.Definition_21_8

-- Declarations for this item will be appended below by the statement pipeline.

open Filter MeasureTheory

universe u

namespace ProbabilityTheory

variable {Ω : Type u} [MeasurableSpace Ω]

namespace IsBrownianMotion

-- Proof sketch: prove the upper bound by the reflection principle and Borel--Cantelli along a
-- geometric time grid, prove the lower bound from independent increments along a sparse geometric
-- subsequence, and then compare arbitrary times with the geometric times while letting the grid
-- ratio tend to `1` and `∞` in the two directions.
/-- Theorem 22.1: for Brownian motion `B`, the law of the iterated logarithm holds:
`limsup_{t → ∞} B_t / sqrt(2 t log log t) = 1` almost surely. -/
theorem ae_limsup_div_sqrt_two_mul_t_log_log_eq_one
    {μ : Measure Ω} {B : NNReal → Ω → ℝ} (hB : IsBrownianMotion μ B) :
    ∀ᵐ ω ∂μ,
      limsup
        (fun t : NNReal ↦
          B t ω / Real.sqrt (2 * (t : ℝ) * Real.log (Real.log (t : ℝ))))
        atTop = 1 := sorry

end IsBrownianMotion

end ProbabilityTheory
