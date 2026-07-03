import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Example_17_59 (from Items/Chap17) -/
open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory unitInterval

noncomputable section

namespace ProbabilityTheory

/-- The number of coordinates among `n` unit-interval samples that fall below the threshold `p`. -/
def binomialUniformCount (n : ℕ) (p : I) : (Fin n → I) → ℕ :=
  fun y ↦ ∑ i, if y i ≤ p then 1 else 0

-- Proof sketch: each summand `y ↦ if y i ≤ p then 1 else 0` is measurable because evaluation at a
-- coordinate is measurable and `ℕ` carries the discrete measurable space; finite sums preserve
-- measurability.
/-- The threshold-count map is measurable on the finite unit cube `I^n`. -/
theorem measurable_binomialUniformCount (n : ℕ) (p : I) :
    Measurable (binomialUniformCount n p) := sorry

-- Proof sketch: the random set `{i < n | Y_i ≤ p}` is `p`-Bernoulli on `Set.Iio n` under the
-- product unit-interval law, and its cardinality is exactly `binomialUniformCount n p`; mapping by
-- the cardinality recovers the canonical binomial law `Bin(n, p)`.
/-- Counting i.i.d. unit-interval uniforms below a threshold `p` gives the binomial law
`Bin(n, p)`. -/
theorem hasLaw_binomialUniformCount (n : ℕ) (p : I) :
    HasLaw (binomialUniformCount n p) (Bin(n, p))
      (ProbabilityMeasure.pi
        (fun _ : Fin n ↦ (⟨(volume : Measure I), inferInstance⟩ : ProbabilityMeasure I)) :
          Measure (Fin n → I)) := sorry

-- Proof sketch: if `p₁ ≤ p₂`, then every coordinate contributing to the count at threshold `p₁`
-- also contributes at threshold `p₂`; comparing the summands termwise yields the inequality of the
-- total counts.
/-- Raising the threshold from `p₁` to `p₂` can only increase the threshold count. -/
theorem binomialUniformCount_mono (n : ℕ) {p₁ p₂ : I} (hp : p₁ ≤ p₂) (y : Fin n → I) :
    binomialUniformCount n p₁ y ≤ binomialUniformCount n p₂ y := sorry

-- Proof sketch: pair the two measurable count maps `binomialUniformCount n p₁` and
-- `binomialUniformCount n p₂`; measurability is preserved under products.
/-- The simultaneous threshold-count map is measurable on the finite unit cube `I^n`. -/
theorem measurable_binomialUniformCountPair (n : ℕ) (p₁ p₂ : I) :
    Measurable
      (fun y : Fin n → I ↦ (binomialUniformCount n p₁ y, binomialUniformCount n p₂ y)) := sorry

/-- The canonical coupling of `Bin(n, p₁)` and `Bin(n, p₂)` obtained by counting the same
independent unit-interval uniforms below the two thresholds. -/
def binomialSuccessParameterCoupling (n : ℕ) (p₁ p₂ : I) : ProbabilityMeasure (ℕ × ℕ) :=
  ProbabilityMeasure.map
    (ProbabilityMeasure.pi
      (fun _ : Fin n ↦ (⟨(volume : Measure I), inferInstance⟩ : ProbabilityMeasure I)))
    (measurable_binomialUniformCountPair n p₁ p₂).aemeasurable

-- Proof sketch: push forward the product unit-interval law by the paired count map
-- `fun y ↦ (binomialUniformCount n p₁ y, binomialUniformCount n p₂ y)`; the two marginals are
-- identified using
-- `hasLaw_binomialUniformCount`, and the almost-sure order follows from the pointwise monotonicity
-- `binomialUniformCount_mono`.
/-- Example 17.59: if `0 ≤ p₁ ≤ p₂ ≤ 1`, then counting the same independent uniform random
variables below the two thresholds produces a coupling of `Bin(n, p₁)` and `Bin(n, p₂)` supported
on the order relation `x₁ ≤ x₂`; hence `Bin(n, p₁)` is stochastically dominated by
`Bin(n, p₂)`. -/
theorem binomial_success_parameter_coupling (n : ℕ) {p₁ p₂ : I} (hp : p₁ ≤ p₂) :
    IsCoupling (binomialSuccessParameterCoupling n p₁ p₂)
      ⟨Bin(n, p₁), inferInstance⟩
      ⟨Bin(n, p₂), inferInstance⟩ ∧
    ∀ᵐ z ∂ (binomialSuccessParameterCoupling n p₁ p₂ : Measure (ℕ × ℕ)), z.1 ≤ z.2 := sorry

-- Proof sketch: realize `Bin(n, p)` by counting threshold hits in `n` common unit-interval
-- samples and `Bin(m, p)` by counting only the first `m` of those same samples; the first count
-- is pointwise bounded by the second, so the induced laws admit an increasing coupling.
/-- For fixed success parameter `p`, binomial laws are stochastically monotone in the number of
trials: if `m ≤ n`, then `Bin(m, p)` admits an increasing coupling with `Bin(n, p)`. -/
theorem binomial_monotone_in_number_of_trials {m n : ℕ} (hmn : m ≤ n) (p : I) :
    ∃ μ : ProbabilityMeasure (ℕ × ℕ),
      IsCoupling μ ⟨Bin(m, p), inferInstance⟩ ⟨Bin(n, p), inferInstance⟩ ∧
        ∀ᵐ z ∂ (μ : Measure (ℕ × ℕ)), z.1 ≤ z.2 := sorry

end ProbabilityTheory
