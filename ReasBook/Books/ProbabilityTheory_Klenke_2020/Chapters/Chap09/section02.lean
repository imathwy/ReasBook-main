import Mathlib
import Mathlib.Probability.Martingale.Basic
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Exercise_9_2_1 (from Items/Chap09) -/
/- Exercise 9.2.1: the textbook conditional-expectation process is the canonical mathlib
martingale `MeasureTheory.martingale_condExp`. Since mathlib totalizes conditional expectation,
the owner statement has no separate integrability hypothesis. -/
recall MeasureTheory.martingale_condExp

/-! ### Exercise_9_2_2 (from Items/Chap09) -/
/- Exercise 9.2.2: a predictable discrete-time martingale is almost surely constant in time, so
for every `n : ℕ` one has `X n = X 0` almost surely. This is exactly the canonical mathlib result
`MeasureTheory.Martingale.eq_zero_of_predictable'`. -/
recall MeasureTheory.Martingale.eq_zero_of_predictable'

/-! ### Remark_9_2 (from Items/Chap09) -/
universe u v w

variable {ι : Type u} {Ω : Type v} {E : Type w}
variable [MeasurableSpace Ω] [MeasurableSpace E]

/- Remark 9.2: this is a terminological recall of the chapter's owner abstraction for stochastic
processes with arbitrary index set. The primitive data is just a family `ι → Ω → E`, and the
separate random-variable condition is recorded by `IsStochasticProcess`. -/
recall IsStochasticProcess

/- Companion specification: `IsStochasticProcess X` means exactly that every coordinate `X i` is
measurable. -/
recall isStochasticProcess_iff

/-! ### Exercise_9_2_3 (from Items/Chap09) -/
open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory

noncomputable section

universe u v

variable {ι : Type u} {Ω : Type v} [Preorder ι]
variable {m0 : MeasurableSpace Ω}
variable {ℱ : Filtration ι m0} {μ : Measure Ω}

-- Proof sketch: combine the submartingale inequality `X s ≤ E[X t | ℱ s]` with conditional
-- Jensen for the convex map `φ`; monotonicity of `φ` lets one pass from `X s ≤ E[X t | ℱ s]` to
-- `φ (X s) ≤ φ (E[X t | ℱ s])`, and the positive-part integrability assumption upgrades the
-- resulting a.e. inequality to the submartingale API.
section

variable [SigmaFiniteFiltration μ ℱ]

/-- Exercise 9.2.3 (1): if `X` is a submartingale and `φ : ℝ → ℝ` is convex and monotone
increasing, then integrability of the positive part of `φ ∘ X_t` at every time implies that the
process `φ(X_t)` is a submartingale. -/
theorem submartingale_convex_monotone_comp {X : ι → Ω → ℝ} {φ : ℝ → ℝ}
    (hX : Submartingale X ℱ μ) (hφ : ConvexOn ℝ Set.univ φ) (hφ_mono : Monotone φ)
    (hφ_int : ∀ i, Integrable (fun ω ↦ (φ (X i ω))⁺) μ) :
    Submartingale (fun i ω ↦ φ (X i ω)) ℱ μ := sorry

end

/-- The deterministic two-time process taking the values `-1` and then `0` on the one-point
probability space. -/
def square_counterexample_process : Fin 2 → PUnit → ℝ
  | 0, _ => -1
  | 1, _ => 0

/-- The trivial two-time filtration on the one-point measurable space used for the monotonicity
counterexample. -/
abbrev square_counterexample_filtration : Filtration (Fin 2) (⊤ : MeasurableSpace PUnit) := ⊥

/-- The Dirac probability measure at the unique point of `PUnit`. -/
abbrev square_counterexample_measure : Measure PUnit := Measure.dirac PUnit.unit

-- Proof sketch: on the one-point space with the trivial filtration, conditional expectations are
-- ordinary values. The deterministic path `-1 ≤ 0` therefore defines a submartingale.
/-- The deterministic two-time process `(-1, 0)` is a submartingale on the one-point space. -/
theorem square_counterexample_process_submartingale :
    Submartingale square_counterexample_process square_counterexample_filtration
      square_counterexample_measure := sorry

-- Proof sketch: `x ↦ x^2` is convex on `ℝ` by the standard polynomial convexity criterion.
/-- The square map is convex on all of `ℝ`. -/
theorem square_counterexample_function_convex :
    ConvexOn ℝ Set.univ (fun x : ℝ ↦ x ^ 2) := sorry

-- Proof sketch: compare the values at `-1` and `0`; monotonicity would force
-- `(-1)^2 ≤ 0^2`, which is false.
/-- The square map is not monotone increasing on `ℝ`. -/
theorem square_counterexample_function_not_monotone :
    ¬ Monotone (fun x : ℝ ↦ x ^ 2) := sorry

-- Proof sketch: the one-point measure turns integrability into finiteness of a single real value,
-- and the transformed process only takes the values `1` and `0`.
/-- The positive part of the transformed counterexample process is integrable at each time. -/
theorem square_counterexample_comp_pos_integrable :
    ∀ i, Integrable
      (fun ω ↦ ((square_counterexample_process i ω) ^ 2)⁺)
      square_counterexample_measure := sorry

-- Proof sketch: after applying `x ↦ x^2`, the deterministic path becomes `1` then `0`, so the
-- one-step submartingale inequality fails already at times `0 ≤ 1`.
/-- Exercise 9.2.3 (2): the deterministic two-time submartingale `(-1, 0)` on the one-point
space together with the convex but nonmonotone map `x ↦ x^2` shows that monotonicity of `φ` is
essential, because the transformed process is not a submartingale. -/
theorem square_counterexample_transform_not_submartingale :
    ¬ Submartingale
      (fun i ω ↦ (square_counterexample_process i ω) ^ 2)
      square_counterexample_filtration square_counterexample_measure := sorry

/-! ### Exercise_9_2_4 (from Items/Chap09) -/
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
