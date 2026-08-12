import ProbabilityTheory_Klenke_2020.Chap12.Remark_12_2

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory

universe u

noncomputable section

/-- The explicit equality-case family on `Fin n`: the `i`-th random variable is the indicator of
the event that the sampled state equals `i`. -/
def exchangeableCovarianceEqualityExample (n : ℕ) : Fin n → Fin n → ℝ :=
  fun i ω ↦ if ω = i then 1 else 0

private theorem two_le_ne_zero {n : ℕ} (h_n : 2 ≤ n) : n ≠ 0 := by
  omega

/-- The uniform probability law on the nonempty finite space `Fin n` used for the equality
example. -/
def exchangeableCovarianceEqualityExampleLaw (n : ℕ) (h_nz : n ≠ 0) :
    ProbabilityMeasure (Fin n) :=
  let _ : NeZero n := ⟨h_nz⟩
  ⟨(PMF.uniformOfFintype (Fin n)).toMeasure, inferInstance⟩

-- Proof sketch: under the uniform law on `Fin n`, permuting the coordinate labels simply permutes
-- the atoms of the sample space, so the finite-dimensional laws of the indicator family are
-- unchanged.
/-- The indicator family on the uniform finite space is exchangeable. -/
theorem exchangeableCovarianceEqualityExample_isExchangeable (n : ℕ) (h_nz : n ≠ 0) :
    IsExchangeable (exchangeableCovarianceEqualityExample n)
      (exchangeableCovarianceEqualityExampleLaw n h_nz) := sorry

-- Proof sketch: the sample space `Fin n` is finite and the indicator variables take only the
-- values `0` and `1`, hence every coordinate belongs to `L²`.
/-- Every coordinate of the explicit equality example is square integrable. -/
theorem exchangeableCovarianceEqualityExample_memLp (n : ℕ) (h_nz : n ≠ 0) :
    ∀ i, MemLp (exchangeableCovarianceEqualityExample n i) 2
      (exchangeableCovarianceEqualityExampleLaw n h_nz) := sorry

-- Proof sketch: under the uniform law each indicator has success probability `1 / n`, so its
-- variance is `((n - 1) / n^2)`, which is positive for `n ≥ 2`.
/-- Every coordinate of the explicit equality example has nonzero variance. -/
theorem exchangeableCovarianceEqualityExample_variance_ne_zero (n : ℕ) (h_n : 2 ≤ n) :
    ∀ i, Var[exchangeableCovarianceEqualityExample n i;
      exchangeableCovarianceEqualityExampleLaw n (two_le_ne_zero h_n)] ≠ 0 := sorry

variable {Ω : Type u} [MeasurableSpace Ω]

-- Proof sketch: apply nonnegativity of `Var[∑ i : Fin n, X i; μ]`, expand it by
-- `ProbabilityTheory.variance_sum`, and use exchangeability to identify every diagonal term with
-- `Var[X₁; μ]` and every off-diagonal term with `cov[X₁, X₂; μ]`.
/-- Exercise 12.1.3 (1): for an exchangeable square-integrable family `X₁, …, Xₙ`, the covariance
between two distinct coordinates is bounded below by `-(n - 1)⁻¹ Var[X₁]`. -/
theorem cov_ge_neg_inv_mul_var_of_exchangeable
    (μ : Measure Ω) [IsProbabilityMeasure μ] {n : ℕ} (X : Fin n → Ω → ℝ)
    {i j : Fin n} (hij : i ≠ j) (h_exchangeable : IsExchangeable X μ)
    (h_memLp : ∀ k, MemLp (X k) 2 μ) :
    cov[X i, X j; μ] ≥ -((1 : ℝ) / (n - 1 : ℝ)) * Var[X i; μ] := sorry

-- Proof sketch: for the explicit indicator family on the uniform finite space, one has
-- `E[X₁ X₂] = 0`, `E[X₁] = 1 / n`, and `Var[X₁] = (n - 1) / n^2`, so the covariance equals
-- `-1 / n^2 = -(n - 1)⁻¹ Var[X₁]`.
/-- Exercise 12.1.3 (2): for `n ≥ 2`, the indicator family on the uniform sample space `Fin n`
provides a nontrivial exchangeable square-integrable example attaining equality in (12.6). -/
theorem exchangeable_indicator_example_attains_covariance_bound (n : ℕ) (h_n : 2 ≤ n)
    {i j : Fin n} (hij : i ≠ j) :
    cov[exchangeableCovarianceEqualityExample n i,
        exchangeableCovarianceEqualityExample n j;
        exchangeableCovarianceEqualityExampleLaw n (two_le_ne_zero h_n)] =
      -((1 : ℝ) / (n - 1 : ℝ)) * Var[exchangeableCovarianceEqualityExample n i;
        exchangeableCovarianceEqualityExampleLaw n (two_le_ne_zero h_n)] := sorry

end
