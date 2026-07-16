import Mathlib
import ProbabilityTheory_Klenke_2020.AchimKlenkeLean.Items.Chap16.Definition_16_1
import ProbabilityTheory_Klenke_2020.AchimKlenkeLean.Items.Chap16.Theorem_16_6

-- Declarations for this item will be appended below by the statement pipeline.

open Filter MeasureTheory ProbabilityTheory
open scoped Topology

section

variable {φ : ℝ → ℂ} {φs : ℕ+ → ℝ → ℂ}

-- Proof sketch: for each positive integer `n`, realize `φs n` as the characteristic function of
-- a probability measure `μₙ`. Since `(φs n)^n = φ`, the measures `μₙ` are `n`th convolution roots
-- of a fixed infinitely divisible law, so Lévy's continuity theorem forces `μₙ` to converge
-- weakly to `δ₀`. The compact-uniform convergence of the characteristic functions then follows
-- from the weak-convergence-to-uniform-on-compacts theorem for characteristic functions.
/-- Exercise 16.1.2 (1): if `φₙ` is a CFP for each positive integer `n` and
`φₙ(t)^n = φ(t)` for every real `t`, then `φₙ → 1` uniformly on every compact subset of `ℝ`. -/
theorem cfp_power_roots_tendstoUniformlyOn_one
    (hcfp : ∀ n : ℕ+, IsCFP (φs n))
    (hpow : ∀ n : ℕ+, ∀ t : ℝ, (φs n t) ^ (n : ℕ) = φ t) :
    ∀ K : Set ℝ, IsCompact K →
      TendstoUniformlyOn (fun n t ↦ φs n t) (fun _ : ℝ ↦ (1 : ℂ)) atTop K := sorry

end

-- Proof sketch: choose the positive-integer roots supplied by `IsInfinitelyDivisibleCFP φ` and
-- apply `cfp_power_roots_tendstoUniformlyOn_one` to them. If `φ t = 0`, then every root vanishes
-- at `t`, contradicting convergence to `1` on the compact singleton `{t}`.
/-- Exercise 16.1.2 (2): an infinitely divisible characteristic function on `ℝ` has no zeros. -/
theorem infinitelyDivisibleCFP_ne_zero
    {φ : ℝ → ℂ} (hφ : IsInfinitelyDivisibleCFP φ) :
    ∀ t : ℝ, φ t ≠ 0 := sorry

namespace MeasureTheory.ProbabilityMeasure

/-- The characteristic function of an infinitely divisible probability law on `ℝ` has no zeros. -/
theorem charFun_ne_zero_of_isInfinitelyDivisible {μ : ProbabilityMeasure ℝ}
    (hμ : IsInfinitelyDivisible μ) :
    ∀ t : ℝ, charFun (μ : Measure ℝ) t ≠ 0 := by
  intro t
  exact infinitelyDivisibleCFP_ne_zero (charFun_isInfinitelyDivisible hμ) t

end MeasureTheory.ProbabilityMeasure
