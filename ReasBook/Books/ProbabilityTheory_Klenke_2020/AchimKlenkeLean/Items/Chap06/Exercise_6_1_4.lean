import ProbabilityTheory_Klenke_2020.AchimKlenkeLean.Items.Chap05.Theorem_5_28

-- Declarations for this item will be appended below by the statement pipeline.

open Filter MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory Topology

universe u

variable {Ω : Type u} [MeasurableSpace Ω]

noncomputable section

-- Proof sketch: the variances of the partial sums are the finite sums of the summable variance
-- series because the terms are independent and centered, so the partial sums form a Cauchy family
-- in `L²`. Use completeness of `L²` to obtain a square-integrable limit and then apply the
-- almost-sure convergence criterion from summable square-integrable tails.
/-- Exercise 6.1.4: If `X₁, X₂, …` is an independent sequence of centered square-integrable real
random variables with summable variances, then the partial sums converge almost surely to a
square-integrable random variable. In Lean's `0`-based indexing, the conclusion concerns the
canonical partial sums `partialSum X n = X₀ + ⋯ + Xₙ₋₁`. -/
theorem exists_memLp_two_ae_tendsto_partial_sums_of_iIndepFun_summable_variance
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℕ → Ω → ℝ)
    (hX_indep : iIndepFun X P)
    (hX_memLp : ∀ n, MemLp (X n) 2 P)
    (hX_centered : ∀ n, P[X n] = 0)
    (h_var_summable : Summable fun n ↦ Var[X n; P]) :
    ∃ Y : Ω → ℝ, MemLp Y 2 P ∧
      ∀ᵐ ω ∂P, Tendsto (fun n ↦ partialSum X n ω) atTop (𝓝 (Y ω)) := sorry
