import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory
open scoped BigOperators ProbabilityTheory unitInterval

universe u

variable {Ω : Type u} {m0 : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
variable {ℱ : Filtration ℕ m0}

/- Clause (1) is `source-facing` through the conditional-law owner abstraction: the corrected main
statement is the existence of a `{-1,1}`-valued Markov kernel with conditional mean `x`, defined
over the law of `X`. The `Ω × I` realization is kept only as a `bridge/view` consequence. -/
/-- Exercise 9.2.4 (1): If a real random variable `X` satisfies `|X| ≤ 1` almost surely, then its
law admits a `{-1,1}`-valued conditional kernel with mean `x`. -/
theorem exists_signed_kernel_with_mean_of_abs_le_one {X : Ω → ℝ}
    (hX_meas : Measurable X) (hX_bdd : ∀ᵐ ω ∂μ, |X ω| ≤ 1) :
    ∃ κ : Kernel ℝ ℝ, IsMarkovKernel κ ∧
      (∀ᵐ x ∂(μ.map X), κ x (({-1} : Set ℝ) ∪ {1}) = (1 : ENNReal)) ∧
      (fun x ↦ ∫ y, y ∂κ x) =ᵐ[μ.map X] fun x ↦ x := sorry

-- Proof sketch: realize the kernel from `exists_signed_kernel_with_mean_of_abs_le_one` on the
-- product extension `Ω × I`; the resulting random variable has that kernel as its conditional law
-- given `X ∘ Prod.fst`, hence its conditional expectation is `X ∘ Prod.fst`.
/-- Bridge for Exercise 9.2.4 (1): after adjoining an auxiliary unit-interval coordinate, the
canonical two-point conditional law can be realized by a `{-1, 1}`-valued random variable whose
conditional expectation with respect to `X ∘ Prod.fst` is `X ∘ Prod.fst`. -/
theorem exists_signed_condexp_eq_of_abs_le_one_prod_extension {X : Ω → ℝ}
    (hX_meas : Measurable X) (hX_bdd : ∀ᵐ ω ∂μ, |X ω| ≤ 1) :
    ∃ Y : Ω × I → ℝ, Measurable Y ∧ Set.range Y ⊆ ({-1, 1} : Set ℝ) ∧
      (μ.prod (volume : Measure I))[Y |
          MeasurableSpace.comap (X ∘ Prod.fst) (borel ℝ)] =ᵐ[μ.prod (volume : Measure I)]
        X ∘ Prod.fst := sorry

-- Proof sketch: use the product-extension conditional-Bernoulli bridge above, or equivalently apply the
-- owner theorem
-- `hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero` to the interval `[-1,1]`. The additional
-- `cosh` bound is the textbook refinement preceding the Gaussian estimate
-- `Real.cosh_le_exp_half_sq`.
/-- Exercise 9.2.4 (2): If `|X| ≤ 1` almost surely and `X` has mean zero, then
`E[e^{t X}] ≤ cosh t ≤ e^{t^2 / 2}` for every real `t`. -/
theorem mgf_le_cosh_and_cosh_le_exp_half_sq_of_abs_le_one {X : Ω → ℝ}
    (hX_meas : AEMeasurable X μ) (hX_bdd : ∀ᵐ ω ∂μ, |X ω| ≤ 1) (hX_mean : μ[X] = 0) :
    ∀ t : ℝ,
      mgf X μ t ≤ Real.cosh t ∧
        Real.cosh t ≤ Real.exp (t ^ 2 / 2) := sorry

-- Proof sketch: this is the source-facing mgf consequence of the owner theorem
-- `HasSubgaussianMGF.sum_of_hasCondSubgaussianMGF`, applied to the martingale increments
-- `M (k + 1) - M k`, whose boundedness yields conditional sub-Gaussian parameters `c k ^ 2`.
/-- Exercise 9.2.4 (3): A martingale starting at `0` and with almost surely bounded increments
has Gaussian moment-generating-function bounds. -/
theorem martingale_mgf_le_exp_half_mul_sum_sq_of_bounded_increments {M : ℕ → Ω → ℝ}
    (hM : Martingale M ℱ μ) (hM0 : M 0 = 0) (c : ℕ → NNReal)
    (hinc : ∀ n, ∀ᵐ ω ∂μ, |M (n + 1) ω - M n ω| ≤ c (n + 1)) :
    ∀ n : ℕ,
      ∀ t : ℝ,
        mgf (M n) μ t ≤
          Real.exp ((t ^ 2 / 2) * ∑ k ∈ Finset.Icc 1 n, ((c k : ℝ)) ^ 2) := sorry

-- Proof sketch: combine the source-facing mgf bound from clause (3), or directly the owner lemma
-- `measure_sum_ge_le_of_hasCondSubgaussianMGF`, with the standard two-sided exponential-Markov
-- argument.
/-- Exercise 9.2.4 (4): Under the bounded-increment hypotheses, the martingale satisfies Azuma's
inequality. -/
theorem azuma_inequality_of_bounded_martingale_increments {M : ℕ → Ω → ℝ}
    (hM : Martingale M ℱ μ) (hM0 : M 0 = 0) (c : ℕ → NNReal)
    (hinc : ∀ n, ∀ᵐ ω ∂μ, |M (n + 1) ω - M n ω| ≤ c (n + 1)) :
    ∀ n : ℕ,
      ∀ ε : ℝ,
        0 ≤ ε →
          μ.real {ω | ε ≤ |M n ω|} ≤
            2 * Real.exp (-ε ^ 2 / (2 * ∑ k ∈ Finset.Icc 1 n, ((c k : ℝ)) ^ 2)) := sorry
