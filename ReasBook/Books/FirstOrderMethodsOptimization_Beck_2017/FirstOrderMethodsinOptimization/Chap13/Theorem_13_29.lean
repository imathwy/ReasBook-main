import Mathlib
import FirstOrderMethodsOptimization_Beck_2017.FirstOrderMethodsinOptimization.Chap01.Definition_1_37
import FirstOrderMethodsOptimization_Beck_2017.FirstOrderMethodsinOptimization.Chap11.Definition_11_14
import FirstOrderMethodsOptimization_Beck_2017.FirstOrderMethodsinOptimization.Chap13.Algorithm_13_7
import FirstOrderMethodsOptimization_Beck_2017.FirstOrderMethodsinOptimization.Chap13.Assumption_13_28
import FirstOrderMethodsOptimization_Beck_2017.FirstOrderMethodsinOptimization.Chap13.Definition_13_17

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe v w

open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory ENNReal RBPG
open GeneralizedBlockConditionalGradient

section

variable {Ξ : Type w} [MeasurableSpace Ξ] {μ : Measure Ξ} [IsProbabilityMeasure μ]
variable {ι : Type v} [Fintype ι] [MeasurableSpace ι] [DiscreteMeasurableSpace ι]
variable {Ei : ι → Type v}
variable [∀ i, NormedAddCommGroup (Ei i)]
variable [∀ i, InnerProductSpace ℝ (Ei i)]
variable [∀ i, CompleteSpace (Ei i)]

local notation "X" => PiLp 2 Ei

/- `prompt_add/` is absent in this workspace, so the declaration shape is sampled from the nearby
Chapter 13 RGBCG owners and the Chapter 11 expected-rate theorem for randomized block methods.
This item is `source-facing`: it states the expected sublinear bounds for RGBCG under Assumption
13.28, using the existing owner abstractions

- `IsGeneralizedBlockConditionalGradientProblem` for Assumption 13.28;
- `GeneralizedBlockConditionalGradient.blockGradient` for the canonical Chapter 11 block-gradient
  bridge attached to the RGBCG smooth term;
- `is_randomized_generalized_block_conditional_gradient_trajectory` for the realized RGBCG sample
  path;
- `composite_model_objective f (PiLp.separableSum g)` for `F(x)`;
- `S[g, blockGradient f](x)` from Definition 13.17 for the chapter quantity `S(x)`;
- `‖·‖_[Li]` from Chapter 11 Definition 11.14 for the weighted block norm.

The stochastic layer is kept at the same abstraction level as Chapter 11: a probability space
together with measurable uniformly sampled block indices on the canonical discrete measurable
space of the finite label type `ι`, a pathwise iterate process, and the per-step sampled-block
minimizers used along that path, rather than a new packaged random-process owner. As in Chapter
11's expected-rate theorem, integrability of each scalar observable whose expectation appears in
the conclusion is kept as theorem-level input instead of being hidden behind a second stochastic
owner. -/

variable {f : X → EReal} {g : (i : ι) → Ei i → EReal}
variable {Li : (i : ι) → PosReal}

section

variable {sampled_block : ℕ → Ξ → ι} {x : ℕ → Ξ → X}
variable {point : (k : ℕ) → (ω : Ξ) → Ei (sampled_block k ω)}
variable {t : ℕ → Set.Icc (0 : ℝ) 1}

local notation "F" => composite_model_objective f (PiLp.separableSum g)
local notation "domG" => effective_domain (PiLp.separableSum g)
local notation "Fopt" => generalized_conditional_gradient_optimal_value f (PiLp.separableSum g)
local notation "FoptReal" => EReal.toReal Fopt
local notation "N" => Fintype.card ι

variable (hproblem : IsGeneralizedBlockConditionalGradientProblem f g Li)
variable (x0 : X)
variable (hx0 : x 0 = fun _ ↦ x0)
variable
  (htraj : ∀ ω,
    is_randomized_generalized_block_conditional_gradient_trajectory
      g (blockGradient f) (fun k ↦ x k ω) (fun k ↦ sampled_block k ω) (fun k ↦ point k ω) t)
variable
  (h_stepsize : ∀ k : ℕ, (t k : ℝ) = (2 * N : ℝ) / (k + 2 * N : ℕ))
variable (h_sampled_block_meas : ∀ k, Measurable (sampled_block k))
variable (h_sampled_block_indep : iIndepFun sampled_block μ)
variable
  (h_sampled_block_uniform :
    ∀ k (i : ι), μ ((sampled_block k) ⁻¹' {i}) = 1 / (N : ℝ≥0∞))
variable {Ω : ℝ}
variable
  (hΩ : ∀ u ∈ domG, ∀ v ∈ domG,
    ‖u - v‖_[Li] ≤ Ω)

local notation "rateBound" =>
  max
    ((((N - 1 : ℕ) : ℝ) * (EReal.toReal (F x0) - FoptReal)))
    (((N : ℝ) * Ω ^ (2 : ℕ)))

-- Proof sketch: combine the one-step expected descent inequality from the RGBCG update with the
-- uniform block-sampling average, the diameter bound `‖u - v‖_L ≤ Ω`, and the deterministic
-- stepsize formula `t_k = 2 |ι| / (k + 2 |ι|)`. Then apply the same scalar recursion lemma as in
-- the deterministic generalized conditional-gradient proof, with
-- `a_k = E[F(x^k)] - F_opt` and `b_k = E[S(x^k)]`.
/-- Theorem 13.29 (1): clause (a). Under Assumption 13.28, if `x^k` is the RGBCG iterate process
with deterministic stepsizes `t_k = 2 |ι| / (k + 2 |ι|)`, and if `Ω` bounds the diameter of
`dom(g)` in the weighted norm `‖·‖_L`, then for every `k ≥ 1` the expected objective gap satisfies
`E(F(x^k)) - F_opt ≤ 2 max{(|ι| - 1)(F(x^0) - F_opt), |ι| Ω^2} / (k + 2 |ι| - 2)`. The
expectation is stated only after explicitly assuming integrability of the scalar observable
`ω ↦ (F (x^k(ω))).toReal`. -/
theorem randomized_generalized_block_conditional_gradient_expected_objective_gap_le_sublinear_rate
    {k : ℕ} (hk : 1 ≤ k)
    (h_objective_integrable :
      Integrable (fun ω ↦ (F (x k ω)).toReal) μ) :
    μ[fun ω ↦ (F (x k ω)).toReal] - FoptReal ≤
      ((2 : ℝ) * rateBound) / ((k + 2 * N - 2 : ℕ) : ℝ) := sorry

-- Proof sketch: apply the same recursion as in clause `(1)` and then invoke the half-tail
-- estimate for sequences satisfying
-- `a_{k+1} ≤ a_k - α_k b_k + (|ι| α_k^2 / 2) Ω^2` with `α_k = 2 / (k + 2 |ι|)`. The result
-- yields an index `n ∈ {⌊k / 2⌋ + 2, …, k}` where the expected block conditional-gradient norm is
-- bounded by the claimed `O(1 / k)` constant; this is equivalent to the textbook minimum
-- formulation.
/-- Theorem 13.29 (2): clause (b). Under the same hypotheses, for every `k ≥ 3` there exists an
index `n ∈ {⌊k / 2⌋ + 2, …, k}` such that
`E(S(x^n)) ≤ 8 max{(|ι| - 1)(F(x^0) - F_opt), |ι| Ω^2} / (k - 2)`; equivalently, the minimum of
`E(S(x^n))` on that half-tail interval obeys the same bound. The theorem therefore assumes
integrability of the scalar observable `ω ↦ (S(x^n(ω))).toReal` for each index on that interval,
matching the Chapter 11 expected-value surface. -/
theorem exists_half_tail_rgbcg_expected_norm_le_sublinear_rate
    {k : ℕ} (hk : 3 ≤ k)
    (h_gap_integrable :
      ∀ n ∈ Set.Icc (k / 2 + 2) k,
        Integrable (fun ω ↦ (S[g, blockGradient f](x n ω)).toReal) μ) :
    ∃ n ∈ Set.Icc (k / 2 + 2) k,
      μ[fun ω ↦ (S[g, blockGradient f](x n ω)).toReal] ≤
        ((8 : ℝ) * rateBound) / ((k - 2 : ℕ) : ℝ) := sorry

end

end
