import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Exercise_5_2_1 (from Items/Chap05) -/
open MeasureTheory ProbabilityTheory
open scoped BigOperators ProbabilityTheory unitInterval

universe u

variable {Ω : Type u} [MeasurableSpace Ω]

noncomputable section

section BernsteinChernoff

variable (P : Measure Ω) [IsProbabilityMeasure P]
variable {n : ℕ} (p : Fin n → I) (X : Fin n → Ω → ℝ)
variable (hX_indep : iIndepFun X P) (hX_law : ∀ i, HasLaw (X i) (Bin(ℝ, 1, p i)) P)

local notation "m" => ∑ i, (p i : ℝ)

-- Proof sketch: apply the Chernoff bound `measure_ge_le_exp_mul_mgf` to the finite sum
-- `ω ↦ ∑ i, X i ω`, use independence to factor its moment generating function into a product of
-- Bernoulli moment generating functions, bound each factor by the textbook expression, and then
-- optimize over the exponential parameter `λ > 0`.
/-- Exercise 5.2.1 (1): for independent Bernoulli random variables `X₁, …, Xₙ` with success
parameters `p₁, …, pₙ`, the upper tail of the partial sum is bounded by the Bernstein--Chernoff
estimate `P[Sₙ ≥ (1 + δ)m] ≤ (exp δ / (1 + δ)^(1 + δ))^m`, where
`Sₙ = ∑ᵢ Xᵢ` and `m = ∑ᵢ pᵢ = 𝔼[Sₙ]`. -/
theorem bernoulli_sum_upper_tail_le_bernstein_chernoff
    {δ : ℝ} (hδ : 0 < δ) :
    P.real {ω | (1 + δ) * m ≤ ∑ i, X i ω} ≤
      Real.rpow (Real.exp δ / Real.rpow (1 + δ) (1 + δ)) m := sorry

-- Proof sketch: apply the lower-tail Chernoff bound `measure_le_le_exp_mul_mgf` to the same sum,
-- equivalently to the upper tail of its negative, factor the moment generating function using
-- independence and the Bernoulli laws, then optimize the resulting exponential estimate to obtain
-- the standard quadratic bound `exp (-δ² m / 2)`.
/-- Exercise 5.2.1 (2): for independent Bernoulli random variables `X₁, …, Xₙ` with success
parameters `p₁, …, pₙ`, the lower tail of the partial sum satisfies
`P[Sₙ ≤ (1 - δ)m] ≤ exp (-δ² m / 2)`, where `Sₙ = ∑ᵢ Xᵢ` and
`m = ∑ᵢ pᵢ = 𝔼[Sₙ]`. -/
theorem bernoulli_sum_lower_tail_le_bernstein_chernoff
    {δ : ℝ} (hδ : 0 < δ) :
    P.real {ω | (∑ i, X i ω) ≤ (1 - δ) * m} ≤
      Real.exp (-(δ ^ 2) * m / 2) := sorry

end BernsteinChernoff

/-! ### Remark_5_2 (from Items/Chap05) -/
open MeasureTheory ProbabilityTheory

universe u

variable {Ω : Type u} [MeasurableSpace Ω]
variable {μ : Measure Ω} [IsFiniteMeasure μ]
variable {X Y : Ω → ℝ}

-- Proof sketch: use `MemLp.mono_exponent` to lower the exponent from `n` to `k`, then apply
-- `MemLp.integrable_norm_pow'` and rewrite the real norm as the absolute value.
/-- Remark 5.2 (1): on a finite measure space, if `X ∈ L^n`, then every absolute moment of order
`k ≤ n` is finite. In particular, the textbook probability-space clause for `1 ≤ k ≤ n` is a
special case, giving the finiteness behind the notation `M_k`. -/
theorem integrable_abs_pow_of_memLp {n k : ℕ} (hX : MemLp X n μ) (hkn : k ≤ n) :
    Integrable (fun ω ↦ |X ω| ^ k) μ := by
  simpa [Real.norm_eq_abs] using
    (hX.mono_exponent (by exact_mod_cast hkn)).integrable_norm_pow'

section Probability

variable [IsProbabilityMeasure μ]

/- Remark 5.2 (2): if `X, Y ∈ L²(μ)`, then their product `XY` is integrable, so the covariance is
well-defined. This is the canonical Hölder consequence `MemLp.integrable_mul`. -/
recall MemLp.integrable_mul

/- Remark 5.2 (3): for square-integrable real random variables on a probability space, covariance
can be written as `𝔼[XY] - 𝔼[X] 𝔼[Y]`. This is the canonical theorem
`covariance_eq_sub`. -/
recall covariance_eq_sub

/- Remark 5.2 (4): variance is the covariance of a real random variable with itself. This is the
canonical identity `covariance_self`. -/
recall covariance_self

end Probability
