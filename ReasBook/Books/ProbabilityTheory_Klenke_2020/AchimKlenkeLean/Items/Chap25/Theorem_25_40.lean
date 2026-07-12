import Mathlib
import ProbabilityTheory_Klenke_2020.Items.Chap21.Exercise_21_4_4
import ProbabilityTheory_Klenke_2020.Items.Chap25.Theorem_25_38

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory

noncomputable section

universe u

namespace ProbabilityTheory

variable {Ω : Type u} [MeasurableSpace Ω]
variable {d : ℕ}

local notation "State" => EuclideanSpace ℝ (Fin d)
local notation "VectorProcess" => NNReal → Ω → State

-- Proof sketch: translate the ball center to `0`, identify the event that the Brownian path
-- started from `x` enters `Metric.ball y r` with finiteness of the positive-time hitting time
-- `τ_[W, Metric.ball y r]`, apply Theorem 25.38 to the concentric annulus between radii `r` and
-- `R`, and then let `R → ∞`.
/-- Theorem 25.40: for `r > 0` and points `x y : State` with `r < dist x y`, the probability that
the Brownian path started from `x` ever enters the open ball `Metric.ball y r`, equivalently that
the positive-time hitting time `τ_[W, Metric.ball y r]` is finite, is `1` in dimensions `d ≤ 2`
and `(r / dist x y)^(d - 2)` in dimensions `d > 2`. -/
theorem brownian_hits_ball_probability
    (μ : ProbabilityMeasure Ω) (W : VectorProcess) (x : State)
    (hW : IsBrownianMotionVectorStartedAt (μ : Measure Ω) W x)
    (r : ℝ) (hr : 0 < r) (y : State) (hxy : r < dist x y) :
    (μ : Measure Ω) {ω | (τ_[W, Metric.ball y r]) ω < ⊤} =
      if d ≤ 2 then 1 else ENNReal.ofReal ((r / dist x y) ^ (d - 2)) := sorry

end ProbabilityTheory
