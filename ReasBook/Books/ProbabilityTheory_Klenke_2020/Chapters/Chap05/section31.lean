

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Remark_5_31 (from Items/Chap05) -/
open Filter MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory Topology ENNReal

noncomputable section

-- Proof sketch: use a sharpness construction for the Rademacher--Menshov criterion to obtain a
-- probability law on `ℝ^ℕ` whose coordinate process is pairwise independent, mean zero, square
-- integrable, has variance `1`, and whose normalized partial sums diverge with almost-sure
-- limsup `⊤`.
/-- Remark 5.31: condition (5.14) is sharp. In the canonical `0`-based Lean indexing, if
`a 0, a 1, …` is a monotone nonnegative normalizing sequence for which the logarithmically
weighted inverse-square `ℝ≥0∞`-series is not summable, then there exists a probability measure on
`ℝ^ℕ` whose coordinate process is pairwise independent, square-integrable, centered, has unit
variance, and whose normalized absolute partial sums have almost-sure limsup `⊤`. Writing the
divergence condition in `ℝ≥0∞` keeps the source-faithful behavior that an index with `a n = 0`
forces divergence as soon as `log (n + 1) > 0`, while `a 0 = 0` is harmless because `log 1 = 0`.
For the textbook indexing `a₁, a₂, …`, apply this statement to `fun n ↦ a (n + 1)`. -/
theorem
    exists_pairwiseIndependent_centered_unitVariance_counterexample_of_not_summable_log_weight_sq
    (a : ℕ → NNReal) (ha_mono : Monotone a)
    (ha_not_summable :
      ¬ Summable
        (fun n : ℕ ↦
          ENNReal.ofReal ((Real.log (n + 1)) ^ 2) * ((a n : ℝ≥0∞) ^ 2)⁻¹)) :
    ∃ P : ProbabilityMeasure (ℕ → ℝ),
      Pairwise (fun i j ↦ coordinateProcess i ⟂ᵢ[P] coordinateProcess j) ∧
      (∀ n, MemLp (coordinateProcess n) 2 P) ∧
      (∀ n, IsCentered (coordinateProcess n) P) ∧
      (∀ n, Var[coordinateProcess n; P] = 1) ∧
      ∀ᵐ ω ∂P.toMeasure,
        limsup
          (fun n : ℕ ↦
            ENNReal.ofReal |partialSum coordinateProcess (n + 1) ω| * ((a n : ℝ≥0∞)⁻¹))
          atTop = ⊤ := sorry

end
