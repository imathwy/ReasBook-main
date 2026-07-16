import Mathlib
import ProbabilityTheory_Klenke_2020.AchimKlenkeLean.Items.Chap13.Definition_13_21

-- Declarations for this item will be appended below by the statement pipeline.

open Filter MeasureTheory Set
open scoped Topology

noncomputable section

namespace StieltjesFunction

/-- The left-continuous inverse, or quantile function, of a real distribution function. It is
defined by the infimum of the superlevel set `{x | u ≤ F x}`. -/
def leftInverse (F : StieltjesFunction ℝ) (u : ℝ) : ℝ :=
  sInf {x : ℝ | u ≤ F x}

-- Proof sketch: if `u ≤ v`, then the superlevel set `{x | v ≤ F x}` is contained in
-- `{x | u ≤ F x}`. Taking infima of these nested superlevel sets yields monotonicity on `(0,1)`.
/-- The left-continuous inverse of a distribution function is monotone on the open unit interval.
-/
theorem monotoneOn_leftInverse
    (F : StieltjesFunction ℝ) [IsDistributionFunction F] :
    MonotoneOn F.leftInverse (Ioo (0 : ℝ) 1) := sorry

-- Proof sketch: apply the standard theorem that a monotone real function has at most countably
-- many discontinuities, restricted to the interval `(0,1)`, to the monotone quantile function.
/-- The left-continuous inverse of a distribution function is continuous for Lebesgue-almost every
parameter `u ∈ (0,1)`. -/
theorem ae_continuousWithinAt_leftInverse
    (F : StieltjesFunction ℝ) [IsDistributionFunction F] :
    ∀ᵐ u ∂(volume.restrict (Ioo (0 : ℝ) 1)),
      ContinuousWithinAt F.leftInverse (Ioo (0 : ℝ) 1) u := sorry

end StieltjesFunction

section

open StieltjesFunction

variable {Fs : ℕ → StieltjesFunction ℝ} {F : StieltjesFunction ℝ}

-- Proof sketch: combine the continuity-point convergence encoded in
-- `distribution_function_weakly_converges_to` with the defining infimum formula for the
-- left-continuous inverses. Continuity of the limit inverse at `u` lets the two-sided squeezing
-- argument for quantiles pass to the limit.
/-- Exercise 13.2.13 (1): if distribution functions `Fₙ` converge weakly to `F`, then their
left-continuous inverses converge at every continuity point of the limit inverse on `(0,1)`. -/
theorem tendsto_leftInverse_of_weak_convergence :
    Π hF : IsDistributionFunction F,
      Π hFs : ∀ n, IsDistributionFunction (Fs n),
        distribution_function_weakly_converges_to Fs F →
        {u : ℝ} →
          (hu : u ∈ Ioo (0 : ℝ) 1) →
          (hcont : ContinuousWithinAt F.leftInverse (Ioo (0 : ℝ) 1) u) →
          Tendsto (fun n ↦ (Fs n).leftInverse u) atTop (𝓝 (F.leftInverse u)) := sorry

-- Proof sketch: by the previous theorem, convergence of the inverses fails only at points where
-- the limit inverse is discontinuous. The exceptional set is Lebesgue-null because the quantile
-- function is monotone on `(0,1)`.
/-- Exercise 13.2.13 (2): consequently, the left-continuous inverses converge for
Lebesgue-almost every `u ∈ (0,1)`. -/
theorem ae_tendsto_leftInverse_of_weak_convergence :
    Π hF : IsDistributionFunction F,
      Π hFs : ∀ n, IsDistributionFunction (Fs n),
        distribution_function_weakly_converges_to Fs F →
    ∀ᵐ u ∂(volume.restrict (Ioo (0 : ℝ) 1)),
      Tendsto (fun n ↦ (Fs n).leftInverse u) atTop (𝓝 (F.leftInverse u)) := sorry

end
