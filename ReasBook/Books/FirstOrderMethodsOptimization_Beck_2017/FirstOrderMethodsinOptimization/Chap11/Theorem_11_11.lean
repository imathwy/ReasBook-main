import Mathlib
import FirstOrderMethodsOptimization_Beck_2017.Chap11.Algorithm_11_5
import FirstOrderMethodsOptimization_Beck_2017.Chap11.Definition_11_14
import FirstOrderMethodsOptimization_Beck_2017.Chap11.Lemma_11_3
import FirstOrderMethodsOptimization_Beck_2017.Chap11.Theorem_11_10
import FirstOrderMethodsOptimization_Beck_2017.Chap11.Theorem_11_2
import FirstOrderMethodsOptimization_Beck_2017.Chap08.Definition_8_2

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe v w

open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory ENNReal RBPG BigOperators Gradient

section

variable {Ω : Type w} {ι : Type*} [Fintype ι] [MeasurableSpace ι] [DiscreteMeasurableSpace ι]
variable {Ei : ι → Type v}
variable [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
variable [∀ i, NormedAddCommGroup (Ei i)] [∀ i, InnerProductSpace ℝ (Ei i)]
variable [∀ i, ProperSpace (Ei i)]
variable {Li : ι → PosReal}

variable {f : ((i : ι) → Ei i) → EReal} {g : (i : ι) → Ei i → EReal}
variable {block_gradient : (i : ι) → ((j : ι) → Ei j) → Ei i}
variable {XStar : Set ((i : ι) → Ei i)} {FOpt : ℝ}

/- Theorem 11.11 is `source-facing`: it states the expected sublinear objective-gap estimate for
the Chapter 11 randomized block proximal-gradient method under i.i.d. uniform block sampling. The
`core/canonical` owners are already `RandomizedBlockProximalGradientAssumptions` for the blockwise
problem data, `IsBlockProximalGradientProblem.interior_effective_domain_point` for the canonical
bridge from the primitive initial datum `x0 ∈ effective_domain (separableSum g)` to
`interior (effective_domain f)`, `randomized_block_proximal_gradient_method` for the pathwise
iterates, and the Chapter 11 `RBPG` weighted-norm notation `‖·‖_[L]`. This file therefore keeps
only the probabilistic theorem surface and reuses those owners directly. For the sampled block
labels, the source-facing i.i.d. uniform semantics live over the canonical discrete measurable
space on the finite index type, so the independence hypothesis `iIndepFun sampled_block μ` and the
singleton-fiber uniform law refer to the same block events. The stochastic regularity layer
remains theorem-level: the theorem assumes integrability of the sampled objective value directly,
without introducing a second public owner for that scalar observable. -/

section

variable (hproblem : RandomizedBlockProximalGradientAssumptions f g block_gradient XStar FOpt Li)
variable (x0 : effective_domain (separableSum g))
variable (sampled_block : ℕ → Ω → ι)

local notation "x0I" => hproblem.interior_effective_domain_point x0
local notation "x[" k "]" =>
  fun ω ↦
    randomized_block_proximal_gradient_method
      hproblem.toIsBlockProximalGradientProblem
      x0I
      (fun n ↦ sampled_block n ω)
      k

local notation "F" =>
  composite_model_objective f (separableSum g)

/-- Helper for Theorem 11.11: the source Lyapunov quantity
`E[(1 / 2) ‖x^k - x*‖_[L]^2 + F(x^k) - F_opt]`. -/
abbrev rbpg_expected_lyapunov
    (xStar : (i : ι) → Ei i) : ℕ → ℝ :=
  fun n ↦
    μ[fun ω ↦
      (1 / 2 : ℝ) * ‖x[n] ω - xStar‖_[Li] ^ (2 : ℕ) +
        (F (x[n] ω)).toReal - FOpt]

/-- Helper for Theorem 11.11: the expected objective gap `E[F(x^k)] - F_opt`. -/
abbrev rbpg_expected_objective_gap : ℕ → ℝ :=
  fun n ↦ μ[fun ω ↦ (F (x[n] ω)).toReal] - FOpt

/-- Helper for Theorem 11.11: the `k`-th RBPG iterate depends only on the first `k` sampled
blocks, encoded by `randomized_block_history`. -/
lemma rbpg_iterate_eq_history_eval
    (k : ℕ) :
    ∃ Φk : (Fin k → ι) → ((i : ι) → Ei i),
      ∀ ω,
        x[k] ω =
          Φk (randomized_block_history (fun n ↦ sampled_block n ω) k) := by
  -- TODO: construct the history evaluator by induction on `k`, using the Chapter 11 one-step
  -- RBPG recursion and the fact that the `(k + 1)`-history extends the `k`-history by one block.
  sorry

/-- Helper for Theorem 11.11: the textbook Lyapunov recursion plus monotonicity of the expected
objective gap implies the `O(1 / k)` scalar bound with factor `N / (N + k + 1)`. -/
lemma sublinear_bound_of_monotone_expected_lyapunov_recursion
    {A B : ℕ → ℝ} {N : ℕ}
    (hN : 0 < N)
    (h_gap_antitone : ∀ n, B (n + 1) ≤ B n)
    (h_gap_le_lyapunov : ∀ n, B (n + 1) ≤ A (n + 1))
    (h_recursion : ∀ n, A (n + 1) ≤ A n - B n / (N : ℝ))
    (k : ℕ) :
    B (k + 1) ≤ (N : ℝ) / (N + k + 1 : ℝ) * A 0 := by
  -- TODO: telescope the scalar recursion, lower-bound the accumulated gap terms by monotonicity,
  -- and isolate `B (k + 1)` exactly as in the textbook proof of (11.u161).
  sorry

/-- Helper for Theorem 11.11: once the expected Lyapunov sequence and expected objective-gap
sequence satisfy the source recursion and monotonicity, the abstract scalar lemma yields the
displayed `O(1 / k)` estimate. -/
lemma rbpg_expected_objective_gap_le_sublinear_of_scalar_recursion
    (xStar : (i : ι) → Ei i)
    (hcard : 0 < Fintype.card ι)
    (h_gap_antitone :
      ∀ n,
        rbpg_expected_objective_gap (μ := μ) hproblem x0 sampled_block (n + 1) ≤
          rbpg_expected_objective_gap (μ := μ) hproblem x0 sampled_block n)
    (h_gap_le_lyapunov :
      ∀ n,
        rbpg_expected_objective_gap (μ := μ) hproblem x0 sampled_block (n + 1) ≤
          rbpg_expected_lyapunov (μ := μ) hproblem x0 sampled_block xStar (n + 1))
    (h_recursion :
      ∀ n,
        rbpg_expected_lyapunov (μ := μ) hproblem x0 sampled_block xStar (n + 1) ≤
          rbpg_expected_lyapunov (μ := μ) hproblem x0 sampled_block xStar n -
            rbpg_expected_objective_gap (μ := μ) hproblem x0 sampled_block n /
              (Fintype.card ι : ℝ))
    (k : ℕ) :
    rbpg_expected_objective_gap (μ := μ) hproblem x0 sampled_block (k + 1) ≤
      (Fintype.card ι : ℝ) / (Fintype.card ι + k + 1 : ℝ) *
        ((1 / 2 : ℝ) * ‖(x0 : ((i : ι) → Ei i)) - xStar‖_[Li] ^ (2 : ℕ) +
          (F x0).toReal - FOpt) := by
  -- Apply the abstract scalar lemma to the Chapter 11 expectation sequences `A` and `B`.
  simpa [rbpg_expected_lyapunov, rbpg_expected_objective_gap,
    randomized_block_proximal_gradient_method_zero,
    IsBlockProximalGradientProblem.interior_effective_domain_point_coe] using
    sublinear_bound_of_monotone_expected_lyapunov_recursion
      (A := fun n ↦ rbpg_expected_lyapunov hproblem x0 sampled_block xStar n)
      (B := fun n ↦ rbpg_expected_objective_gap hproblem x0 sampled_block n)
      hcard
      h_gap_antitone
      h_gap_le_lyapunov
      h_recursion
      k

/-- Helper for Theorem 11.11: a sampled-block process on a probability space forces the finite
block index set to be nonempty, hence to have positive cardinality. -/
lemma rbpg_block_index_card_pos_of_sampled_block
    (ω0 : Ω)
    (sampled_block' : ℕ → Ω → ι) :
    0 < Fintype.card ι := by
  -- Evaluating the sampled block map at one sample point produces a witness in `ι`.
  exact Fintype.card_pos_iff.mpr ⟨sampled_block' 0 ω0⟩

/-- Helper for Theorem 11.11: every realized RBPG iterate stays in the effective domain of the
block-separable regularizer, so the source one-step inequalities can be applied pathwise. -/
lemma rbpg_iterate_mem_effective_domain
    (k : ℕ) :
    ∀ ω, x[k] ω ∈ effective_domain (separableSum g) := by
  induction k with
  | zero =>
      intro ω
      -- The initial iterate is the prescribed effective-domain point `x⁰ = x0`.
      simpa using x0.2
  | succ k hk =>
      intro ω
      -- One RBPG step is a single block-coordinate prox update, which preserves the domain.
      change
        block_coordinate_update
          (x[k] ω)
          (sampled_block k ω)
          (hproblem.toIsBlockProximalGradientProblem.prox_point
              (Li (sampled_block k ω))
              (sampled_block k ω)
              (x[k] ω) -
            x[k] ω (sampled_block k ω)) ∈
          effective_domain (separableSum g)
      simpa using
        hproblem.toIsBlockProximalGradientProblem.block_coordinate_update_prox_point_mem_effective_domain
          (Li (sampled_block k ω))
          ⟨x[k] ω, hk ω⟩
          (sampled_block k ω)

/-- Helper for Theorem 11.11: the finite sampled-block history up to time `n - 1` is independent
of the current sampled block `i_n`, so their joint law splits as a product measure. -/
lemma randomized_block_history_current_block_jointlaw
    (n : ℕ)
    (h_sampled_block_meas : ∀ k, Measurable (sampled_block k))
    (h_sampled_block_indep : iIndepFun sampled_block μ) :
    μ.map
        (fun ω ↦
          (randomized_block_history (fun m ↦ sampled_block m ω) n, sampled_block n ω)) =
      (μ.map (fun ω ↦ randomized_block_history (fun m ↦ sampled_block m ω) n)).prod
        (μ.map (sampled_block n)) := by
  -- TODO: use `iIndepFun.indepFun_finset` on `Finset.range n` and `{n}`, then compose the
  -- subtype-valued process with the canonical maps to `randomized_block_history` and `sampled_block n`.
  sorry

/-- Helper for Theorem 11.11: averaging over the current sampled block after freezing the finite
history `ξ_{n-1}` gives the uniform block average from the source proof. -/
lemma randomized_block_history_current_block_average
    (n : ℕ)
    (ψ : (Fin n → ι) → ι → ℝ)
    (h_sampled_block_meas : ∀ k, Measurable (sampled_block k))
    (h_sampled_block_indep : iIndepFun sampled_block μ)
    (h_sampled_block_uniform :
      ∀ k (i : ι), μ ((sampled_block k) ⁻¹' {i}) = 1 / (Fintype.card ι : ℝ≥0∞)) :
    μ[fun ω ↦ ψ (randomized_block_history (fun m ↦ sampled_block m ω) n) (sampled_block n ω)] =
      μ[fun ω ↦ ((Fintype.card ι : ℝ)⁻¹) *
        (∑ i, ψ (randomized_block_history (fun m ↦ sampled_block m ω) n) i)] := by
  -- TODO: push the observable through the joint law of `(ξ_{n-1}, i_n)` and collapse the
  -- current-block marginal to the uniform finite average over `ι`.
  sorry

/-- Helper for Theorem 11.11: a real observable depending only on a finite block history is
integrable because that history takes values in the finite discrete type `Fin k → ι`. -/
lemma randomized_block_history_observable_integrable
    (k : ℕ) (ψ : (Fin k → ι) → ℝ) :
    Integrable (fun ω ↦ ψ (randomized_block_history (fun n ↦ sampled_block n ω) k)) μ := by
  -- TODO: prove the history map is measurable coordinatewise and then use that its codomain is
  -- finite, so every real-valued observable on `Fin k → ι` is integrable after pushforward.
  sorry

/-- Helper for Theorem 11.11: every realized RBPG objective value is finite, so the source
objective decrease can be transported through `EReal.toReal`. -/
lemma rbpg_iterate_objective_finite
    (k : ℕ) (ω : Ω) :
    F (x[k] ω) ≠ ⊤ ∧ F (x[k] ω) ≠ ⊥ := by
  -- TODO: combine effective-domain finiteness for `f` and `separableSum g` with the standard
  -- `EReal` arithmetic rules to show the composite objective never hits `±∞` along RBPG iterates.
  sorry

/-- Helper for Theorem 11.11: the sampled objective observable factors through a finite history,
so its integrability reduces to the finite-history adapter above. -/
lemma rbpg_objective_observable_integrable
    (k : ℕ) :
    Integrable (fun ω ↦ (F (x[k] ω)).toReal) μ := by
  -- TODO: rewrite `x^k` as a finite-history observable via `rbpg_iterate_eq_history_eval` and
  -- then apply `randomized_block_history_observable_integrable` to the induced scalar observable.
  sorry

/-- Helper for Theorem 11.11: the sampled weighted squared distance also factors through a finite
history, so it is integrable under the probability measure. -/
lemma rbpg_sqdist_observable_integrable
    (xStar : (i : ι) → Ei i) (k : ℕ) :
    Integrable (fun ω ↦ (1 / 2 : ℝ) * ‖x[k] ω - xStar‖_[Li] ^ (2 : ℕ)) μ := by
  -- TODO: as for the objective observable, factor the weighted squared distance through the
  -- finite history `ξ_{k-1}` and invoke finite-history integrability.
  sorry

/-- Helper for Theorem 11.11: pathwise, one RBPG step does not increase the objective value. -/
lemma rbpg_objective_antitone_pointwise
    (n : ℕ) (ω : Ω) :
    (F (x[n + 1] ω)).toReal ≤ (F (x[n] ω)).toReal := by
  -- TODO: apply the pathwise one-block sufficient-decrease inequality and pass to `toReal`
  -- using `rbpg_iterate_objective_finite`.
  sorry

/-- Helper for Theorem 11.11: pointwise, the Lyapunov integrand dominates the objective-gap
integrand because the weighted squared-distance term is nonnegative. -/
lemma rbpg_objective_gap_integrand_le_lyapunov_integrand
    (xStar : (i : ι) → Ei i) (n : ℕ) :
    ∀ ω,
      (F (x[n + 1] ω)).toReal - FOpt ≤
        (1 / 2 : ℝ) * ‖x[n + 1] ω - xStar‖_[Li] ^ (2 : ℕ) +
          (F (x[n + 1] ω)).toReal - FOpt := by
  intro ω
  -- The source comparison `F(x^{n+1}) - F_opt ≤ (1/2)‖x^{n+1} - x*‖_L^2 + F(x^{n+1}) - F_opt`
  -- is just the nonnegativity of the squared-distance term.
  have hsq_nonneg :
      0 ≤ (1 / 2 : ℝ) * ‖x[n + 1] ω - xStar‖_[Li] ^ (2 : ℕ) := by
    exact mul_nonneg (by norm_num) (sq_nonneg _)
  linarith

/-- Helper for Theorem 11.11: once the objective value and squared-distance observables are
integrable, the pointwise Lyapunov domination upgrades to the expectation-level comparison needed
in the scalar recursion package. -/
lemma rbpg_expected_objective_gap_le_lyapunov_of_integrable
    (xStar : (i : ι) → Ei i) (n : ℕ)
    (h_objective_integrable :
      Integrable (fun ω ↦ (F (x[n + 1] ω)).toReal) μ)
    (h_sqdist_integrable :
      Integrable (fun ω ↦
        (1 / 2 : ℝ) * ‖x[n + 1] ω - xStar‖_[Li] ^ (2 : ℕ)) μ) :
      rbpg_expected_objective_gap (μ := μ) hproblem x0 sampled_block (n + 1) ≤
      rbpg_expected_lyapunov (μ := μ) hproblem x0 sampled_block xStar (n + 1) := by
  -- TODO: subtract `F_opt`, add the nonnegative squared-distance term, and integrate the
  -- pointwise comparison from `rbpg_objective_gap_integrand_le_lyapunov_integrand`.
  sorry

/-- Helper for Theorem 11.11: the remaining source-faithful blocker is to lift the deterministic
one-step RBPG Lyapunov inequality to unconditional expectations through the finite sampled-block
history, and to package the resulting scalar recursion and monotonicity hypotheses. -/
lemma rbpg_expected_scalar_recursion_package
    (xStar : (i : ι) → Ei i) (hxStar : xStar ∈ XStar)
    (h_sampled_block_meas : ∀ k, Measurable (sampled_block k))
    (h_sampled_block_indep : iIndepFun sampled_block μ)
    (h_sampled_block_uniform :
      ∀ k (i : ι), μ ((sampled_block k) ⁻¹' {i}) = 1 / (Fintype.card ι : ℝ≥0∞)) :
    0 < Fintype.card ι ∧
      (∀ n,
        rbpg_expected_objective_gap (μ := μ) hproblem x0 sampled_block (n + 1) ≤
          rbpg_expected_objective_gap (μ := μ) hproblem x0 sampled_block n) ∧
      (∀ n,
        rbpg_expected_objective_gap (μ := μ) hproblem x0 sampled_block (n + 1) ≤
          rbpg_expected_lyapunov (μ := μ) hproblem x0 sampled_block xStar (n + 1)) ∧
      (∀ n,
        rbpg_expected_lyapunov (μ := μ) hproblem x0 sampled_block xStar (n + 1) ≤
          rbpg_expected_lyapunov (μ := μ) hproblem x0 sampled_block xStar n -
            rbpg_expected_objective_gap (μ := μ) hproblem x0 sampled_block n /
              (Fintype.card ι : ℝ)) := by
  -- TODO: combine the already established uniform averaging bridge with the deterministic frozen
  -- one-step Lyapunov inequality to obtain the Chapter 11 scalar recursion package.
  sorry

-- Proof sketch: derive the one-step Lyapunov inequality for
-- `(1 / 2) ‖x^k - x*‖_L^2 + F(x^k) - F_opt`, condition on the history `ξ_{k-1}`, and use the
-- independence and uniformity of the sampled block `i_k` to average the realized update over the
-- current block choice. Iterating the resulting recursion and using the monotonicity of the
-- expected objective values yields the displayed `O(1 / k)` estimate.
/-- Theorem 11.11: for RBPG iterates generated by i.i.d. uniformly sampled blocks, the expected
objective gap satisfies the sublinear estimate
`E[F(x^{k+1})] - F_opt ≤ (|ι| / (|ι| + k + 1)) ((1 / 2) ‖x^0 - x*‖_L^2 + F(x^0) - F_opt)`. -/
theorem randomized_block_proximal_gradient_expected_objective_gap_le_sublinear
    (xStar : (i : ι) → Ei i) (hxStar : xStar ∈ XStar)
    (h_sampled_block_meas : ∀ k, Measurable (sampled_block k))
    (h_sampled_block_indep : iIndepFun sampled_block μ)
    (h_sampled_block_uniform :
      ∀ k (i : ι), μ ((sampled_block k) ⁻¹' {i}) = 1 / (Fintype.card ι : ℝ≥0∞))
    (k : ℕ)
    (h_objective_integrable :
      Integrable (fun ω ↦ (F (x[k + 1] ω)).toReal) μ) :
    μ[fun ω ↦ (F (x[k + 1] ω)).toReal] - FOpt ≤
      (Fintype.card ι : ℝ) / (Fintype.card ι + k + 1 : ℝ) *
        ((1 / 2 : ℝ) * ‖(x0 : ((i : ι) → Ei i)) - xStar‖_[Li] ^ (2 : ℕ) +
          (F x0).toReal - FOpt) :=
by
  rcases
      rbpg_expected_scalar_recursion_package
        hproblem
        x0
        sampled_block
        xStar
        hxStar
        h_sampled_block_meas
        h_sampled_block_indep
        h_sampled_block_uniform with
    ⟨hcard, h_gap_antitone, h_gap_le_lyapunov, h_recursion⟩
  -- The remaining closure is purely scalar once the expected recursion package is available.
  exact
    rbpg_expected_objective_gap_le_sublinear_of_scalar_recursion
      hproblem
      x0
      sampled_block
      xStar
      hcard
      h_gap_antitone
      h_gap_le_lyapunov
      h_recursion
      k

end

end
