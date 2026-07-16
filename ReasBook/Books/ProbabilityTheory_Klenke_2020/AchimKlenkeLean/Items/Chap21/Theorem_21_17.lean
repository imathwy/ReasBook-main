import Mathlib
import ProbabilityTheory_Klenke_2020.AchimKlenkeLean.Items.Chap21.Definition_21_2
import ProbabilityTheory_Klenke_2020.AchimKlenkeLean.Items.Chap21.Definition_21_8

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory
open scoped NNReal

universe u

namespace ProbabilityTheory

variable {Ω : Type u} [MeasurableSpace Ω]

namespace IsBrownianMotion

-- Proof sketch: follow the Paley--Wiener--Zygmund dyadic-block argument from the text. For a
-- fixed exponent `γ > 1 / 2`, estimate the probability that `k` consecutive increments of size
-- `1 / n` are all `O(n^{-γ})`, use independence and the Gaussian scaling law to obtain a summable
-- bound, and conclude by Borel--Cantelli that almost no sample path is `γ`-Hölder at any point.
/-- Theorem 21.17: for every exponent `γ ∈ (0,1]` with `γ > 1 / 2`, almost every Brownian sample
path fails to be Hölder-continuous of order `γ` at every time `t ≥ 0`. -/
theorem ae_forall_not_holderContinuousAt_path
    {μ : Measure Ω} {B : NNReal → Ω → ℝ} (hB : IsBrownianMotion μ B)
    (γ : Set.Ioc (0 : ℝ≥0) 1) (hγ : (1 / 2 : ℝ≥0) < γ) :
    ∀ᵐ ω ∂μ, ∀ t : NNReal, ¬ HolderContinuousAt γ (fun s : NNReal ↦ B s ω) t := sorry

-- Proof sketch: apply `ae_forall_not_holderContinuousAt_path` with any exponent
-- `γ ∈ (1 / 2, 1]`; differentiability of a path at a point on `[0, ∞)` would imply a local
-- Lipschitz estimate there, hence Hölder continuity of every order at most `1`, contradicting the
-- previous theorem.
/-- Brownian sample paths are almost surely nowhere differentiable on the half-line `[0, ∞)`. -/
theorem ae_nowhere_differentiable_path
    {μ : Measure Ω} {B : NNReal → Ω → ℝ} (hB : IsBrownianMotion μ B) :
    ∀ᵐ ω ∂μ, ∀ t : NNReal,
      ¬ DifferentiableWithinAt ℝ (fun s : ℝ ↦ B (Real.toNNReal s) ω) (Set.Ici (0 : ℝ))
        (t : ℝ) := sorry

end IsBrownianMotion

end ProbabilityTheory
