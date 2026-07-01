import Mathlib
import AchimKlenkeLean.Items.Chap21.Definition_21_8

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory

noncomputable section

universe u

namespace ProbabilityTheory

variable {Ω : Type u} [MeasurableSpace Ω]

/-- The first time at which the path of `B` meets the affine boundary `t ↦ a * t + b`. -/
def brownianAffineBoundaryHittingTime (B : NNReal → Ω → ℝ) (a b : ℝ) : Ω → ENNReal :=
  hittingAfter (fun t ω ↦ B t ω - a * (t : ℝ)) ({b} : Set ℝ) (0 : NNReal)

-- Proof sketch: `brownianAffineBoundaryHittingTime` is the canonical hitting time `hittingAfter`
-- for the drifted process `t ↦ B_t - a t` into the singleton level `{b}`.
omit [MeasurableSpace Ω] in
/-- Expanding `brownianAffineBoundaryHittingTime` gives the canonical owner `hittingAfter` for the
drifted process `t ↦ B_t - a t` at the level `b`. -/
theorem brownianAffineBoundaryHittingTime_eq_hittingAfter
    (B : NNReal → Ω → ℝ) (a b : ℝ) :
    brownianAffineBoundaryHittingTime B a b =
      hittingAfter (fun t ω ↦ B t ω - a * (t : ℝ)) ({b} : Set ℝ) (0 : NNReal) := by
  rfl

/-- The samplewise factor `e^{-λτ}` attached to the affine-boundary hitting time `τ`, taken to be
`0` on the event that the boundary is never hit. -/
def brownianAffineBoundaryHittingTimeLaplaceWeight
    (B : NNReal → Ω → ℝ) (a b lam : ℝ) : Ω → ℝ :=
  fun ω ↦
    Set.indicator
      {ω | brownianAffineBoundaryHittingTime B a b ω < ⊤}
      (fun ω ↦ Real.exp (-lam * (brownianAffineBoundaryHittingTime B a b ω).toReal)) ω

-- Proof sketch: unfold `brownianAffineBoundaryHittingTimeLaplaceWeight`.
omit [MeasurableSpace Ω] in
/-- The affine-boundary Laplace weight is the exponential factor on the finite-hitting event and
vanishes otherwise. -/
theorem brownianAffineBoundaryHittingTimeLaplaceWeight_def
    (B : NNReal → Ω → ℝ) (a b lam : ℝ) :
    brownianAffineBoundaryHittingTimeLaplaceWeight B a b lam =
      fun ω ↦
        Set.indicator
          {ω | brownianAffineBoundaryHittingTime B a b ω < ⊤}
          (fun ω ↦ Real.exp (-lam * (brownianAffineBoundaryHittingTime B a b ω).toReal)) ω := by
  rfl

section BrownianMotionExercise

variable {μ : Measure Ω}
variable {B : NNReal → Ω → ℝ}

-- Proof sketch: apply exponential martingales to the drifted process `t ↦ B t - a t`, stop at the
-- first hitting time of level `b`, and use optional stopping. Solving the resulting quadratic
-- equation for the martingale parameter yields the exponent
-- `-b * a - b * sqrt (a ^ 2 + 2 * λ)`.
/-- Exercise 21.2.6 (1): for Brownian motion `B`, if `b > 0` and `τ` is the first time with
`B_t = a t + b`, then the Laplace transform of `τ`, interpreted as `0` on the event `{τ = ∞}`,
is `exp (-b a - b sqrt (a^2 + 2 λ))`. -/
theorem brownianAffineBoundaryHittingTime_laplaceTransform
    (hB : IsBrownianMotion μ B) {a b lam : ℝ} (hb : 0 < b) (hlam : 0 ≤ lam) :
    ∫ ω, brownianAffineBoundaryHittingTimeLaplaceWeight B a b lam ω ∂μ =
      Real.exp (-b * a - b * Real.sqrt (a ^ 2 + 2 * lam)) := sorry

-- Proof sketch: specialize part (1) at `λ = 0`. Then the Laplace weight reduces to the indicator
-- of `{τ < ∞}`, and `sqrt (a ^ 2) = |a|`, so the right-hand side becomes `1` when `a ≤ 0` and
-- `exp (-2 * b * a)` when `a > 0`, equivalently `min 1 (exp (-2 * b * a))`.
/-- Exercise 21.2.6 (2): consequently, the probability that the affine boundary `t ↦ a t + b` is
ever hit is `min (1, exp (-2 b a))`. -/
theorem brownianAffineBoundaryHittingTime_lt_top_prob
    (hB : IsBrownianMotion μ B) {a b : ℝ} (hb : 0 < b) :
    μ {ω | brownianAffineBoundaryHittingTime B a b ω < ⊤} =
      ENNReal.ofReal (min 1 (Real.exp (-2 * b * a))) := sorry

end BrownianMotionExercise

end ProbabilityTheory
