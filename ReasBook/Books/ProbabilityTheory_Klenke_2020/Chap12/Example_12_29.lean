import Mathlib
import ProbabilityTheory_Klenke_2020.Chap12.Example_12_3
import ProbabilityTheory_Klenke_2020.Chap17.Exercise_17_3_1

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory
open scoped BigOperators ProbabilityTheory

universe u

variable {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω]

noncomputable section

-- Proof sketch: condition on the mixing variable `Z`; under `IsConditionallyBernoulliIID`, the
-- first `n` draws have conditional law `Ber_Z^{⊗ n}`, so the conditional probability that all of
-- them are black is `Z^n`. Integrating the conditional probability identifies the `n`th moment of
-- `Z` with the black-prefix probability.
/-- For a `{0,1}`-valued process that is conditionally i.i.d. Bernoulli with parameter `Z`, the
`n`th moment of `Z` is the probability that the first `n` draws are black. -/
private theorem moment_eq_prob_black_prefix_of_isConditionallyBernoulliIID
    {μ : Measure Ω} [IsProbabilityMeasure μ] {X : ℕ → Ω → Bool}
    {Z : Ω → unitInterval} (hX : IsConditionallyBernoulliIID Z X μ) (n : ℕ) :
    μ[fun ω ↦ (Z ω : ℝ) ^ n] =
      (μ {ω | ∀ i : Fin n, X i ω = true}).toReal := sorry

-- Proof sketch: first use
-- `moment_eq_prob_black_prefix_of_isConditionallyBernoulliIID` to identify the moments of `Z`
-- with the probabilities of the events `{X₀ = ⋯ = X_{n-1} = 1}`. The Pólya-urn formula gives
-- these probabilities as `∏_{k=0}^{n-1} (M + k)/(N + k)`, which are exactly the moments of the
-- Beta distribution with parameters `M` and `N - M`; moment determinacy on `[0,1]` then yields
-- the claimed law.
/-- Example 12.29: for Pólya's urn model, if the color indicators are conditionally i.i.d.
Bernoulli given a random parameter `Z` and the black-prefix probabilities are the usual
Pólya-urn products, then `Z` has Beta law with parameters `M` and `N - M`. -/
theorem polyaUrn_limit_hasLaw_beta
    {μ : Measure Ω} [IsProbabilityMeasure μ] {X : ℕ → Ω → Bool}
    {Z : Ω → unitInterval} (hX : IsConditionallyBernoulliIID Z X μ)
    {M N : ℕ} (hM : 0 < M) (hMN : M < N)
    (h_black_prefix : ∀ n : ℕ,
      (μ {ω | ∀ i : Fin n, X i ω = true}).toReal =
        ∏ k ∈ Finset.range n, ((M + k : ℕ) : ℝ) / ((N + k : ℕ) : ℝ)) :
    HasLaw (fun ω ↦ (Z ω : ℝ)) (betaMeasure M (N - M : ℕ)) μ := sorry
