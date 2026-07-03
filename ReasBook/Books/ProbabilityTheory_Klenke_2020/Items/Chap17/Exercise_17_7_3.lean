import ProbabilityTheory_Klenke_2020.Items.Chap17.Theorem_17_60

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory
open scoped ProbabilityTheory unitInterval

noncomputable section

namespace ProbabilityTheory

-- Proof sketch: for the forward implication, specialize the stochastic-order comparison to the
-- increasing indicator of `{1, 2, ...}` and identify the complement event `{0}` for the two
-- laws. For the reverse implication, use the nat-valued characterization of stochastic order by
-- the tail probabilities of a binomial law and a Poisson law, then show that for these two
-- families all tail comparisons reduce to the comparison of the zero atom.
/-- Exercise 17.7.3: the binomial law `b_{n,p}` is below the Poisson law `Poi_λ` in the
stochastic order on `ℕ` if and only if their zero atoms satisfy
`(1 - p)^n ≥ exp(-λ)`. -/
theorem binomial_stochasticLE_poisson_iff_prob_zero_ge (n : ℕ) (p : I) (lam : NNReal) :
    StochasticLE
      (ProbabilityMeasure.toFin1Real
        (⟨Bin(n, p), inferInstance⟩ : ProbabilityMeasure ℕ))
      (ProbabilityMeasure.toFin1Real
        (⟨poissonMeasure lam, inferInstance⟩ : ProbabilityMeasure ℕ)) ↔
      (1 - (p : ℝ)) ^ n ≥ Real.exp (-(lam : ℝ)) := sorry

end ProbabilityTheory
