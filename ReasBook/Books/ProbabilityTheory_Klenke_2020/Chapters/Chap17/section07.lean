import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Exercise_17_7_1 (from Items/Chap17) -/
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

/-! ### Exercise_17_7_2 (from Items/Chap17) -/
open MeasureTheory ProbabilityTheory

noncomputable section

/- Exercise 17.7.2 (first claim): reflexivity is already the chapter stochastic-order owner from
Definition 17.57, specialized to the embedded nat-valued laws. -/
recall stochasticLE_refl

-- Proof sketch: for the forward implication, test the stochastic order with increasing tail or
-- truncated identity functions to recover `λ₁ ≤ λ₂`; for the reverse implication, couple
-- `Poi_{λ₂}` as `Poi_{λ₁} + Poi_{λ₂ - λ₁}` when `λ₁ ≤ λ₂`.
/-- Exercise 17.7.2: the Poisson law with parameter `λ₁` is below the Poisson law with parameter
`λ₂` in the discrete stochastic order on `ℕ` if and only if `λ₁ ≤ λ₂`. -/
theorem poissonMeasure_stochasticLE_iff (lam1 lam2 : NNReal) :
    StochasticLE
      (ProbabilityMeasure.toFin1Real
        (⟨poissonMeasure lam1, inferInstance⟩ : ProbabilityMeasure ℕ))
      (ProbabilityMeasure.toFin1Real
        (⟨poissonMeasure lam2, inferInstance⟩ : ProbabilityMeasure ℕ)) ↔
      lam1 ≤ lam2 := sorry

/-! ### Exercise_17_7_3 (from Items/Chap17) -/
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

/-! ### Example_17_7 (from Items/Chap17) -/
open MeasureTheory ProbabilityTheory

noncomputable section

universe u

/-- Example 17.7: for a rate `θ`, the laws `ν_t^θ = Poi_(θ t)` on `ℕ` form the Poisson
convolution semigroup; a Markov process on `ℕ` with these increment laws is called a Poisson
process with jump rate `θ`. -/
def poissonConvolutionSemigroup (θ : NNReal) : NNReal → ProbabilityMeasure ℕ :=
  fun t ↦ ⟨poissonMeasure (θ * t), inferInstance⟩

-- The primitive data is just the family `t ↦ Poi_(θ t)`; coercing it to a measure is definitional.
/-- The Poisson convolution semigroup at time `t` is the Poisson law with parameter `θ * t`. -/
@[simp] theorem poissonConvolutionSemigroup_toMeasure (θ t : NNReal) :
    (poissonConvolutionSemigroup θ t : Measure ℕ) = poissonMeasure (θ * t) :=
  rfl

instance instIsConvolutionSemigroup_poissonConvolutionSemigroup (θ : NNReal) :
    IsConvolutionSemigroup (poissonConvolutionSemigroup θ) where
  convolution_eq s t := by
    apply ProbabilityMeasure.toMeasure_injective
    rw [ProbabilityMeasure.toMeasure_mul, poissonConvolutionSemigroup_toMeasure,
      poissonConvolutionSemigroup_toMeasure, poissonConvolutionSemigroup_toMeasure,
      poissonMeasure_conv_poissonMeasure]
    simp [mul_add]

/-- The family `t ↦ Poi_(θ t)` is a convolution semigroup on `ℕ`. -/
theorem poissonConvolutionSemigroup_isConvolutionSemigroup (θ : NNReal) :
    IsConvolutionSemigroup (poissonConvolutionSemigroup θ) :=
  inferInstance

variable {Ω : Type u} [MeasurableSpace Ω]

-- The bridge is source-facing: the owner abstraction remains `IsPoissonProcess`, while the
-- semigroup-valued increment hypothesis is just rewritten to the canonical Poisson increment law.
/-- A nondecreasing `ℕ`-valued process whose increment laws are given by the Poisson convolution
semigroup with rate `θ` is a Poisson process with jump rate `θ`. -/
theorem isPoissonProcess_of_poissonConvolutionSemigroup
    {μ : Measure Ω} [IsProbabilityMeasure μ] {θ : NNReal} {X : NNReal → Ω → ℕ}
    (hstochastic : IsStochasticProcess X) (hzero : X 0 = 0) (hmono : Monotone X)
    (hindep : HasIndepIncrements X μ)
    (hsemigroup : ∀ ⦃s t : NNReal⦄, s ≤ t →
      HasLaw (fun ω ↦ X t ω - X s ω) (poissonConvolutionSemigroup θ (t - s)) μ) :
    IsPoissonProcess θ μ X := by
  refine isPoissonProcess_of_textbook hstochastic hzero hmono hindep ?_
  intro s t hst
  simpa using hsemigroup (le_of_lt hst)
