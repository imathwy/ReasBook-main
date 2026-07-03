import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_8_8 (from Chap08) -/
universe u v

section

variable {E : Type u} {α : Type v} [LinearOrder α]

/- Definition 8.8 is `source-facing`: the textbook introduces the running minimum of the attained
objective values along a given iterate sequence `x^0, x^1, ...`. In this domain the canonical
finite-minimum owner is mathlib's `Finset.min'` applied to the image of the prefix
`Finset.range (k + 1)`, so the public API records the best value achieved up to iteration `k`
directly as that finite minimum, without introducing a surrogate wrapper for the iterate history. -/

-- Proof sketch: the prefix index set `Finset.range (k + 1)` contains `0`, hence its image under
-- `n ↦ f (x n)` contains the initial objective value `f (x 0)`.
/-- The finite set of objective values attained up to iteration `k` is nonempty. -/
theorem objective_value_prefix_nonempty (f : E → α) (x : ℕ → E) (k : ℕ) :
    ((Finset.range (k + 1)).image fun n ↦ f (x n)).Nonempty := by
  -- The prefix always contains the initial index `0`.
  refine ⟨f (x 0), Finset.mem_image.mpr ?_⟩
  -- Map that initial index into the finite set of attained objective values.
  exact ⟨0, by simp, rfl⟩

/-- Definition 8.8: the best achieved function value at iteration `k` is the minimum of the
objective values `f (x^n)` over all indices `n = 0, 1, …, k`. -/
def best_achieved_function_value (f : E → α) (x : ℕ → E) (k : ℕ) : α :=
  ((Finset.range (k + 1)).image fun n ↦ f (x n)).min' (objective_value_prefix_nonempty f x k)

/-- Helper for Definition 8.8: each prefix objective value belongs to the image finset of all
objective values attained up to iteration `k`. -/
lemma objective_value_mem_prefix_image
    (f : E → α) (x : ℕ → E) {k n : ℕ} (hn : n ∈ Finset.range (k + 1)) :
    f (x n) ∈ ((Finset.range (k + 1)).image fun m ↦ f (x m)) := by
  -- Record that the value comes from the index `n` already lying in the prefix.
  exact Finset.mem_image.mpr ⟨n, hn, rfl⟩

-- Proof sketch: for `n ≤ k`, the value `f (x n)` belongs to the image of `Finset.range (k + 1)`.
-- Then apply `Finset.min'_le` to the defining finite set of attained objective values.
/-- The best achieved value up to iteration `k` is less than or equal to every objective value
attained by the first `k + 1` iterates. -/
theorem best_achieved_function_value_le_objective_value
    (f : E → α) (x : ℕ → E) (k n : ℕ) (hn : n ∈ Finset.range (k + 1)) :
    best_achieved_function_value f x k ≤ f (x n) := by
  -- Unfold the running minimum so the claim becomes the standard `Finset.min'` bound.
  unfold best_achieved_function_value
  -- Apply the minimum comparison to the member indexed by `n`.
  exact Finset.min'_le _ _ (objective_value_mem_prefix_image f x hn)

end

/-! ### Proposition_8_8 (from Chap08) -/
universe u v

open MeasureTheory
open scoped BigOperators ProbabilityTheory

noncomputable section

section

variable {E : Type u} {Ω : Type v}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
variable [MeasurableSpace E] [BorelSpace E]
variable {f : E → ℝ} {C XStar : Set E} {fOpt δ Θ : ℝ} {m : ℕ}
variable (L : Fin m → ℝ)
variable (h_problem : IsConstrainedConvexProblem (fun x : E ↦ (f x : EReal)) C XStar fOpt)
variable (x : ℕ → Ω → C) (g : ℕ → Ω → E) (t : ℕ → ℝ) (x0 : C)

local notation "x[" k "]" =>
  x k

/- Proposition 8.8 is `bridge/view`: it specializes the general stochastic projected-subgradient
rate from Theorem 8.35 to the finite-sum setting through an explicit bound
`L_tilde_f ≤ δ * √m * √(∑ i, L_{f_i}^2)`. The owner abstractions remain the Chapter 8 running-best
value `best_achieved_function_value`, the standing projected-subgradient problem class, and the
stochastic oracle package; the finite-sum data enter only through the component Lipschitz
constants `L i`. -/

-- Proof sketch: apply Theorem 8.35 (2) to the stochastic projected-subgradient iterates with the
-- prescribed stepsize `t_k = √(2 Θ) / (L_tilde_f √(k + 1))`. Then substitute the finite-sum
-- estimate `L_tilde_f ≤ δ * √m * √(∑ i, L i^2)` into the resulting right-hand side.
/-- Proposition 8.8: if the stochastic projected subgradient oracle along `x^k` has bound constant
`L_tilde_f` controlled by `δ * √m * √(∑ i, L_{f_i}^2)`, then the expected best objective gap of the
first `k + 1` iterates satisfies the finite-sum `O(1 / √k)` estimate
`E(f_best^k) - fOpt ≤ δ √m √(∑ i, L_{f_i}^2) √(2 Θ) / √(k + 2)`. -/
theorem stochastic_projected_subgradient_expected_best_value_gap_le_of_finite_sum_bound
    (h_zero : ∀ ω, x[0] ω = x0)
    (h_succ :
      ∀ k ω,
        x[k + 1] ω =
          metricProjection C h_problem.feasible_nonempty h_problem.feasible_closed.isComplete
            h_problem.feasible_convex ((x[k] ω : E) - t k • g k ω))
    (h_stepsize_pos : ∀ n, 0 < t n)
    (h_oracle :
      StochasticProjectedSubgradientOracle μ f
        (fun n ω ↦ (x[n] ω : E))
        g)
    (hΘ :
      ∀ y ∈ C, ∀ z ∈ C, (1 / 2 : ℝ) * ‖y - z‖ ^ (2 : ℕ) ≤ Θ)
    (h_stepsize :
      ∀ n,
        t n = Real.sqrt (2 * Θ) / (h_oracle.L_tilde_f * Real.sqrt ((n : ℝ) + 1)))
    (h_oracle_bound :
      (2 * (1 + Real.log 3)) * h_oracle.L_tilde_f ≤
        δ * Real.sqrt (m : ℝ) * Real.sqrt (∑ i : Fin m, L i ^ (2 : ℕ)))
    (k : ℕ) (hk : 2 ≤ k) :
    μ[fun ω ↦ best_achieved_function_value f (fun n ↦ (x[n] ω : E)) k] - fOpt ≤
      δ * Real.sqrt (m : ℝ) * Real.sqrt (∑ i : Fin m, L i ^ (2 : ℕ)) *
        Real.sqrt (2 * Θ) / Real.sqrt ((k : ℝ) + 2) := sorry

-- Proof sketch: first apply
-- `stochastic_projected_subgradient_expected_best_value_gap_le_of_finite_sum_bound` to obtain the
-- bound `δ * √m * √(∑ i, L i^2) * √(2 Θ) / √(k + 2)` on the expected best objective gap. Then use
-- the lower bound on `k` to rearrange this rate estimate into an upper bound by `ε`.
/-- If the iteration index is at least the finite-sum complexity threshold from Proposition 8.8,
then the expected best objective gap is at most `ε`. -/
theorem stochastic_projected_subgradient_expected_best_value_gap_le_epsilon_of_finite_sum_iteration_count
    (h_zero : ∀ ω, x[0] ω = x0)
    (h_succ :
      ∀ k ω,
        x[k + 1] ω =
          metricProjection C h_problem.feasible_nonempty h_problem.feasible_closed.isComplete
            h_problem.feasible_convex ((x[k] ω : E) - t k • g k ω))
    (h_stepsize_pos : ∀ n, 0 < t n)
    (h_oracle :
      StochasticProjectedSubgradientOracle μ f
        (fun n ω ↦ (x[n] ω : E))
        g)
    (hΘ :
      ∀ y ∈ C, ∀ z ∈ C, (1 / 2 : ℝ) * ‖y - z‖ ^ (2 : ℕ) ≤ Θ)
    (h_stepsize :
      ∀ n,
        t n = Real.sqrt (2 * Θ) / (h_oracle.L_tilde_f * Real.sqrt ((n : ℝ) + 1)))
    (h_oracle_bound :
      (2 * (1 + Real.log 3)) * h_oracle.L_tilde_f ≤
        δ * Real.sqrt (m : ℝ) * Real.sqrt (∑ i : Fin m, L i ^ (2 : ℕ)))
    (hδ : 0 ≤ δ) (hΘ_nonneg : 0 ≤ Θ)
    {ε : ℝ} (hε : 0 < ε)
    (k : ℕ)
    (hk :
      max
          (δ ^ (2 : ℕ) * (m : ℝ) * (2 * Θ) * (∑ i : Fin m, L i ^ (2 : ℕ)) /
              ε ^ (2 : ℕ) - 2)
          2 ≤
        (k : ℝ)) :
    μ[fun ω ↦ best_achieved_function_value f (fun n ↦ (x[n] ω : E)) k] - fOpt ≤ ε := sorry

end

/-! ### Remark_8_8 (from Chap08) -/
universe u

open scoped Topology

section

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- Remark 8.8: if `f` is convex and the feasible set `C` lies in the interior of `dom(f)`, then
`f` is subdifferentiable at every point of `C`, equivalently `C ⊆ dom(∂ f)`. -/
-- Proof sketch: for each `x ∈ C`, the inclusion `C ⊆ interior (effective_domain f)` gives
-- `x ∈ interior (effective_domain f)`. Apply the interior-point subdifferentiability theorem
-- `subdifferential_nonempty_at_interior_point` and rewrite the conclusion using
-- `mem_subdifferential_domain`.
theorem subset_subdifferential_domain_of_subset_interior_effective_domain
    (f : E → EReal) (C : Set E) (hf_convex : is_convex_function f)
    (hC : C ⊆ interior (effective_domain f)) :
    C ⊆ subdifferential_domain f := by
  intro x hxC
  -- Move from the feasible-set inclusion to interior membership at the chosen point.
  rw [mem_subdifferential_domain]
  -- The interior-point theorem supplies a nonempty subdifferential.
  exact subdifferential_nonempty_at_interior_point f x hf_convex (hC hxC)

/-- If `C` is closed and `f` is closed, then the feasible lower level set
`C ∩ {x | f x ≤ fOpt}` is closed. -/
-- Proof sketch: use `lowerSemicontinuous_iff_isClosed_real_sublevelSets` to show that the real
-- sublevel set `f ⁻¹' Iic (fOpt : EReal)` is closed, then intersect it with the closed feasible
-- set `C`.
theorem isClosed_inter_real_sublevelSet
    (f : E → EReal) (C : Set E) (fOpt : ℝ)
    (hC_closed : IsClosed C) (hf_closed : LowerSemicontinuous f) :
    IsClosed (C ∩ f ⁻¹' Set.Iic (fOpt : EReal)) := by
  -- Closedness of `f` gives closedness of each real sublevel set.
  have hsublevel_closed : IsClosed (f ⁻¹' Set.Iic (fOpt : EReal)) :=
    (lowerSemicontinuous_iff_isClosed_real_sublevelSets f).mp hf_closed fOpt
  -- Intersect the closed feasible set with the closed sublevel set.
  exact hC_closed.inter hsublevel_closed

/-- If the feasible lower level set `C ∩ {x | f x ≤ fOpt}` is nonempty, then every point outside
that set has strictly positive distance to it. -/
-- Proof sketch: first obtain closedness of `C ∩ f ⁻¹' Iic (fOpt : EReal)` from
-- `isClosed_inter_real_sublevelSet`. Then apply the metric-space characterization
-- `IsClosed.notMem_iff_infDist_pos` for nonempty closed sets.
theorem infDist_pos_of_not_mem_inter_real_sublevelSet
    (f : E → EReal) (C : Set E) (fOpt : ℝ)
    (hC_closed : IsClosed C) (hf_closed : LowerSemicontinuous f)
    (hX_nonempty : (C ∩ f ⁻¹' Set.Iic (fOpt : EReal)).Nonempty)
    {x : E} (hx : x ∉ C ∩ f ⁻¹' Set.Iic (fOpt : EReal)) :
    0 < Metric.infDist x (C ∩ f ⁻¹' Set.Iic (fOpt : EReal)) := by
  -- First recover the closedness of the feasible optimal set.
  have hX_closed : IsClosed (C ∩ f ⁻¹' Set.Iic (fOpt : EReal)) :=
    isClosed_inter_real_sublevelSet f C fOpt hC_closed hf_closed
  -- For a nonempty closed set, nonmembership is equivalent to strictly positive distance.
  exact (hX_closed.notMem_iff_infDist_pos hX_nonempty).mp hx

end
