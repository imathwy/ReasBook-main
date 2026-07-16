import ProbabilityTheory_Klenke_2020.AchimKlenkeLean.Items.Chap14.Definition_14_46

-- Declarations for this item will be appended below by the statement pipeline.

open Filter MeasureTheory
open scoped Topology

section

variable {d : ℕ}

namespace IsConvolutionSemigroup

variable {ν : NNReal → ProbabilityMeasure (Fin d → ℝ)} [IsConvolutionSemigroup ν]

/-- Exercise 14.4.2: for every fixed `t ≥ 0`, the subdivided marginals `ν (t / n)` of a
convolution semigroup on the chapter's `ℝ^d` model converge weakly to the Dirac probability
measure at `0` as `n → ∞` through positive integers. -/
-- Proof sketch: write `ν t` as an `n`-fold convolution power of `ν (t / n)` using the semigroup
-- law on `ℝ^d`, then apply the standard infinitesimality criterion for convolution roots of a
-- fixed probability measure in this finite-dimensional real-vector-space setting to conclude weak
-- convergence to `δ₀`.
theorem tendsto_div_pNat_diracProba_zero (t : NNReal) :
    Tendsto (fun n : ℕ+ ↦ ν (t / (n : NNReal))) atTop (𝓝 (diracProba (0 : Fin d → ℝ))) := sorry

end IsConvolutionSemigroup

end
