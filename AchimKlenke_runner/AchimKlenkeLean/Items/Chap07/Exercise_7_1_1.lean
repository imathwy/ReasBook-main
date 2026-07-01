import AchimKlenkeLean.Items.Chap06.Exercise_6_1_4

-- Declarations for this item will be appended below by the statement pipeline.

open Filter MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory Topology

universe u

variable {Ω : Type u} [MeasurableSpace Ω]

noncomputable section

-- Proof sketch: reuse the Chapter 6 `L²` convergence theorem, then replace its almost-sure limit
-- by the canonical measurable representative of the underlying `MemLp` function.
/-- Exercise 7.1.1 (1): (i) If `X₁, X₂, …` is an independent sequence of centered square-integrable
real random variables and `∑ Var[X_i] < ∞`, then the partial sums converge almost surely to a
measurable real-valued limit. In Lean's `0`-based indexing, the partial sums are `partialSum X n
= X₀ + ⋯ + Xₙ₋₁`. -/
theorem hasAETendstoPartialSums_of_iIndepFun_summable_variance
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℕ → Ω → ℝ)
    (hX_indep : iIndepFun X P)
    (hX_memLp : ∀ n, MemLp (X n) 2 P)
    (hX_centered : ∀ n, P[X n] = 0)
    (h_var_summable : Summable fun n ↦ Var[X n; P]) :
    ∃ Y : Ω → ℝ, Measurable Y ∧
      ∀ᵐ ω ∂P, Tendsto (fun n ↦ partialSum X n ω) atTop (𝓝 (Y ω)) := by
  obtain ⟨Y, hY_memLp, hY_lim⟩ :=
    exists_memLp_two_ae_tendsto_partial_sums_of_iIndepFun_summable_variance
      P X hX_indep hX_memLp hX_centered h_var_summable
  let hY_meas := hY_memLp.aestronglyMeasurable
  refine ⟨hY_meas.mk Y, hY_meas.measurable_mk, ?_⟩
  filter_upwards [hY_lim, hY_meas.ae_eq_mk] with ω hω hY_eq
  simpa [hY_eq] using hω

-- Proof sketch: take a product probability measure on `ℝ^ℕ` whose `n`th coordinate is usually
-- `0` but equals `± (n + 1)` with probability of order `(n + 1)⁻²`. Then the coordinates are
-- independent, centered, and square integrable with nonsummable variances, while Borel--Cantelli
-- gives only finitely many nonzero coordinates almost surely, so the partial sums converge almost
-- surely.
/-- Exercise 7.1.1 (2): (ii) The converse in part (i) does not hold: there exists a probability
measure on `ℝ^ℕ` whose coordinate process is independent, centered, and square integrable, whose
partial sums converge almost surely, but whose variance series is not summable. -/
theorem exists_counterexample_to_converse_of_summable_variance
    :
    ∃ P : ProbabilityMeasure (ℕ → ℝ),
      iIndepFun coordinateProcess P ∧
        (∀ n, MemLp (coordinateProcess n) 2 P) ∧
        (∀ n, P[coordinateProcess n] = 0) ∧
        (∃ Y : (ℕ → ℝ) → ℝ, Measurable Y ∧
          ∀ᵐ ω ∂P.toMeasure,
            Tendsto (fun n ↦ partialSum coordinateProcess n ω) atTop (𝓝 (Y ω))) ∧
        ¬ Summable (fun n ↦ Var[coordinateProcess n; P]) := sorry
