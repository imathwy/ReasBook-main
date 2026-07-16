import Mathlib
import ProbabilityTheory_Klenke_2020.AchimKlenkeLean.Items.Chap21.Definition_21_8

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory

noncomputable section

universe u

namespace ProbabilityTheory

variable {Ω : Type u} [MeasurableSpace Ω]

-- Proof sketch: use recurrence of one-dimensional Brownian motion together with continuity of the
-- sample paths to show that one of the two boundary levels is hit in finite time almost surely.
/-- Exercise 21.2.4 (1): for a Brownian motion and levels `a < 0 < b`, the first hitting time of
the boundary set `{a, b}` is almost surely finite. -/
theorem brownianMotion_twoSidedHittingTime_ae_ne_top
    {μ : Measure Ω} {B : NNReal → Ω → ℝ} (hB : IsBrownianMotion μ B)
    {a b : ℝ} (ha : a < 0) (hb : 0 < b) :
    ∀ᵐ ω ∂μ, hittingAfter B ({a, b} : Set ℝ) 0 ω ≠ ⊤ := sorry

-- Proof sketch: apply optional stopping to the Brownian martingale `t ↦ B t` at the exit time
-- `τ_{a,b}`. Since the stopped value can only be `a` or `b`, the mean-zero identity yields the
-- affine equation determining the probability of exiting through `b`.
/-- Exercise 21.2.4 (2): the probability that Brownian motion exits the interval `(a, b)` through
the upper endpoint `b` is `-a / (b - a)`. -/
theorem brownianMotion_twoSidedHittingTime_prob_hit_right
    {μ : Measure Ω} {B : NNReal → Ω → ℝ} (hB : IsBrownianMotion μ B)
    {a b : ℝ} (ha : a < 0) (hb : 0 < b) :
    μ {ω | stoppedValue B (hittingAfter B ({a, b} : Set ℝ) 0) ω = b} =
      ENNReal.ofReal (-a / (b - a)) := sorry

-- Proof sketch: use Exercise 21.2.2 for the martingale `t ↦ B t ^ 2 - t`, stop at `τ_{a,b}`,
-- insert the almost-sure identity `B_{τ_{a,b}} ∈ {a, b}`, and combine it with the exit
-- probability from the previous clause to compute the expected stopping time.
/-- Exercise 21.2.4 (3): the expectation of the two-sided Brownian hitting time `τ_{a,b}` is
`-ab`. -/
theorem brownianMotion_twoSidedHittingTime_expectation_eq
    {μ : Measure Ω} {B : NNReal → Ω → ℝ} (hB : IsBrownianMotion μ B)
    {a b : ℝ} (ha : a < 0) (hb : 0 < b) :
    ∫ ω, ENNReal.toReal (hittingAfter B ({a, b} : Set ℝ) 0 ω) ∂μ = -a * b := sorry

end ProbabilityTheory
