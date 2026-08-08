import ProbabilityTheory_Klenke_2020.Chap17.Definition_17_53

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory unitInterval

noncomputable section

namespace ProbabilityTheory

-- Proof sketch: write `n₂ = k n₁`, partition the `n₂` Bernoulli trials into `k` blocks of length
-- `n₁`, choose the block-success parameter so that the zero-count probability matches
-- `(1 - p₂) ^ n₂`, and couple the `n₁`-count with the number of nonempty blocks to obtain an
-- ordered coupling supported on `{(x₁, x₂) : ℕ × ℕ | x₁ ≤ x₂}`.
/-- Exercise 17.7.1: when `n₁ ∣ n₂`, the condition
`(1 - p₁) ^ n₁ ≥ (1 - p₂) ^ n₂` yields a direct coupling of the binomial laws
`Bin(n₁, p₁)` and `Bin(n₂, p₂)` that is supported on the order relation `x₁ ≤ x₂`, and hence
proves the divisible-case claim of Theorem 17.60. -/
theorem exists_ordered_binomial_coupling_of_pow_condition_of_dvd
    (n₁ n₂ : ℕ+) (p₁ p₂ : I)
    (hdiv : (n₁ : ℕ) ∣ n₂) (hpow : (1 - (p₁ : ℝ)) ^ (n₁ : ℕ) ≥ (1 - (p₂ : ℝ)) ^ (n₂ : ℕ)) :
    ∃ π : ProbabilityMeasure (ℕ × ℕ),
      IsCoupling π
        (⟨Bin((n₁ : ℕ), p₁), inferInstance⟩ : ProbabilityMeasure ℕ)
        (⟨Bin((n₂ : ℕ), p₂), inferInstance⟩ : ProbabilityMeasure ℕ) ∧
        π {x | x.1 ≤ x.2} = 1 := sorry

end ProbabilityTheory
