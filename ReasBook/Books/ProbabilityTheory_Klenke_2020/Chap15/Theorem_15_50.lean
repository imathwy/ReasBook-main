import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open Filter MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory Topology

universe u

noncomputable section

variable {Ω : Type u} [MeasurableSpace Ω]

/- Theorem 15.50 is `source-facing`: it states Kolmogorov's three-series criterion for the
textbook truncations `Yₙ = Xₙ 𝟙_{|Xₙ| ≤ K}`. The primitive data are just the shifted sequence
`X₁, X₂, …`, the cutoff `K`, and the indicator-cutoff random variables themselves. There is no
upstream owner declaration for the whole three-condition package in this chapter or in mathlib, so
the public API is kept as the direct conjunction of the three summability clauses instead of a
parallel wrapper class. For the large-jump condition, the canonical owner abstraction is the real
probability mass `P.real A`; using `Summable` directly on `P A : ℝ≥0∞` would be vacuous. -/

-- Proof sketch: for the forward implication, use Borel--Cantelli for the large-jump events, then
-- combine almost-sure convergence of the truncated centered series with convergence of the series
-- of expectations. For the reverse implication, deduce the tail-probability summability from
-- almost-sure convergence, then apply the centered-series criterion to the truncated variables and
-- recover convergence of the expectation series from the deterministic part of the partial sums.
/-- Theorem 15.50: for independent real random variables `X₁, X₂, …` and the truncations
`Yₙ = Xₙ 𝟙_{|Xₙ| ≤ K}` with `K > 0`, the series `∑ Xₙ` converges almost surely exactly when the
real tail probabilities `∑ P(|Xₙ| > K)` are summable, the series of expectations `∑ E[Yₙ]`
converges, and the series of variances `∑ Var[Yₙ]` is summable. -/
theorem ae_summable_iff_three_series_conditions
    (P : Measure Ω) [IsProbabilityMeasure P]
    (K : ℝ) (hK : 0 < K) (X : ℕ → Ω → ℝ)
    (hX_measurable : ∀ n, Measurable (X (n + 1)))
    (hX_indep : iIndepFun (fun n ↦ X (n + 1)) P) :
    (∀ᵐ ω ∂P, Summable (fun n : ℕ ↦ X (n + 1) ω)) ↔
      Summable (fun n : ℕ ↦ P.real {ω | K < |X (n + 1) ω|}) ∧
        Summable
          (fun n : ℕ ↦ P[Set.indicator {ω | |X (n + 1) ω| ≤ K} (X (n + 1))]) ∧
          Summable
            (fun n : ℕ ↦
              Var[Set.indicator {ω | |X (n + 1) ω| ≤ K} (X (n + 1)); P]) := sorry
