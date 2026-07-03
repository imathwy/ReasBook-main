import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Theorem_23_3 (from Items/Chap23) -/
open Filter MeasureTheory

noncomputable section

universe u

namespace ProbabilityTheory

variable {Ω : Type u} [MeasurableSpace Ω]

variable {P : Measure Ω} {X : ℕ → Ω → ℝ}

-- `bridge/view` layer: the canonical owner in this chapter is the large-deviation principle for
-- `normalizedPartialSumLaw`, available upstream as
-- `normalizedPartialSumLaw_satisfies_cramer_largeDeviationPrinciple` and
-- `cramer_empiricalMean_largeDeviationPrinciple`. The present theorem keeps the textbook
-- upper-tail event phrasing `P[Sₙ ≥ x n]` as a source-facing consequence of that owner API.
--
-- Proof sketch: rewrite the upper-tail event as the half-line `{y | x ≤ y}` for the normalized
-- partial-sum law, then read off the rate from the canonical Cramér LDP owner theorem.
/-- Theorem 23.3: Cramér's theorem for the upper tail of i.i.d. real partial sums with finite
exponential moments under a probability measure. Using the chapter's `0`-based partial sums
`partialSum X n = X₀ + ⋯ + Xₙ₋₁`, the logarithmic asymptotic of `P[Sₙ ≥ x n]` converges to the
negative of the Legendre transform of the cumulant generating function of the common law. -/
theorem cramer_partialSum_largeDeviation_upperTail
    [IsProbabilityMeasure P]
    (hX_iid : IsIID X P)
    (hmgf : ∀ t : ℝ, Integrable (fun ω ↦ Real.exp (t * X 0 ω)) P)
    {x : ℝ} (hx : P[X 0] < x) :
    Tendsto
      (fun n : ℕ ↦ ENNReal.log (P {ω | x * n ≤ partialSum X n ω}) / n)
      atTop
      (nhds (-legendreCgfRateFunction (X 0) P x)) := sorry

end ProbabilityTheory
