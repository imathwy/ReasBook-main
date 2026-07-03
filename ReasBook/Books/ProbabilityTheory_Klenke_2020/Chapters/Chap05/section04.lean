

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Exercise_5_4_1 (from Items/Chap05) -/
open MeasureTheory ProbabilityTheory
open scoped BigOperators ProbabilityTheory

universe u

variable {Ω : Type u} [MeasurableSpace Ω]

noncomputable section

-- Proof sketch: decompose according to the first index where `|S_k|` crosses `t`, compare this
-- event with the large-deviation events for the terminal differences `S_n - S_k`, use
-- independence, and optimize the union bound to obtain the factor `3`.
/-- Exercise 5.4.1: for independent real random variables `X₁, …, Xₙ` with partial sums
`S_k = X₁ + ⋯ + X_k`, Etemadi's inequality bounds the probability that one of the absolute partial
sums reaches `t` by three times the largest tail probability at level `t / 3`. This is the
canonical `0`-based Lean version using the chapter's existing `partialSum`; for the textbook
sequence `X₁, X₂, …`, apply it to `fun k ↦ X (k + 1)`. -/
theorem etemadi_inequality_abs_partial_sums (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℕ → Ω → ℝ) (n : ℕ) (hX_indep : iIndepFun (fun i : Fin n ↦ X i) P) {t : ℝ} (ht : 0 < t) :
    P (absHitEvent X n t) ≤
      3 *
        (Finset.Icc 1 n).sup fun k ↦
          P {ω | t / 3 ≤ |partialSum X k ω|} := sorry

/-! ### Theorem_5_4 (from Items/Chap05) -/
open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory

universe u

variable {Ω : Type u} [MeasurableSpace Ω]

/- Theorem 5.4: if `X` and `Y` are independent integrable real random variables on a probability
space, then the product `XY` is integrable. This is the canonical theorem
`IndepFun.integrable_mul`. -/
recall IndepFun.integrable_mul

variable {μ : Measure Ω} {X Y : Ω → ℝ}

-- Proof sketch: apply the canonical factorization theorem
-- `IndepFun.integral_mul_eq_mul_integral`; the required strong measurability follows from the
-- integrability hypotheses.
/-- Theorem 5.4: if `X` and `Y` are independent integrable real random variables on a probability
space, then their expectation factors as `𝔼[XY] = 𝔼[X] 𝔼[Y]`. -/
theorem expectation_mul_eq_mul_expectation_of_indepFun
    (hXY : X ⟂ᵢ[μ] Y) (hX : Integrable X μ) (hY : Integrable Y μ) :
    μ[X * Y] = μ[X] * μ[Y] :=
  hXY.integral_mul_eq_mul_integral hX.aestronglyMeasurable hY.aestronglyMeasurable

-- Proof sketch: `IndepFun.covariance_eq_zero` is the canonical covariance formulation, and
-- `Definition_5_1` packages uncorrelatedness as square-integrability together with vanishing
-- covariance.
/-- Theorem 5.4: in particular, independent square-integrable real random variables are
uncorrelated. -/
theorem isUncorrelated_of_indepFun
    (hXY : X ⟂ᵢ[μ] Y) (hX : MemLp X 2 μ) (hY : MemLp Y 2 μ) :
    IsUncorrelated X Y μ :=
  ⟨hX, hY, hXY.covariance_eq_zero hX hY⟩
