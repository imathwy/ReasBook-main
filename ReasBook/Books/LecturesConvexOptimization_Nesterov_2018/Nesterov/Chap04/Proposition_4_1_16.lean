import LecturesConvexOptimization_Nesterov_2018.Nesterov.Chap04.Definition_4_1_17

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators

noncomputable section

universe u

variable {X : Type u}

/- Proposition 4.1.16 lies in the finite-horizon conservative cubic-regularization backtracking
complexity domain.

Sampled owner declarations:
* `RegularizedNewton.acceptingParameters` and
  `RegularizedNewton.mem_acceptingParameters_iff` in `Definition_4_1_16`, the canonical
  acceptance-set owner and view;
* `CubicRegularizationBacktracking.acceptingExponents`,
  `CubicRegularizationBacktracking.index`, and
  `CubicRegularizationBacktracking.nextRegularization` in `Definition_4_1_17`, the chapter owner
  API for the accepted-exponent set, its least element, and the conservative update
  `M_(k+1) = max {L₀, hat M_k / 2}`;
* `CubicRegularizationMethod.regularization_mem_Icc` in `Algorithm_4_1_5`, the nearby chapter
  pattern where regularization bounds remain theorem-level trajectory data rather than a second
  local owner.

Best owner abstraction:
* source-facing: the finite-horizon conservative complexity statement for a regularization
  schedule `M₀, …, M_(N+1)` and iterate sequence `x₀, x₁, …`;
* core/canonical: `RegularizedNewton.acceptingParameters` for automatic acceptance and
  `CubicRegularizationBacktracking.nextRegularization` for the conservative parameter update;
* bridge/view: `CubicRegularizationBacktracking.IsNextRegularization`, which records the
  witness-free conservative one-step update used by the finite-horizon trajectory hypotheses.

Primitive data:
* the iterate sequence `x₀, x₁, …`;
* the regularization sequence `M₀, M₁, …`;
* the initial bound `M₀ ∈ [L₀, 2L]`;
* the theorem-level conservative update law
  `IsNextRegularization ... x_k M_k L₀ M_(k+1)`.

Derived API:
* automatic acceptance above `L`, phrased directly through `acceptingParameters`;
* existence of accepted exponents at each step under the automatic-acceptance hypothesis;
* propagated interval bounds, the intrinsic endpoint-ratio control on total backtracking
  increments, and the resulting conservative bound on computed trial maps.

Source/core/bridge triage:
* source-facing: the total-backtracking and total-trial-mapping bounds in Proposition 4.1.16;
* core/canonical: `RegularizedNewton.acceptingParameters` and
  `CubicRegularizationBacktracking.nextRegularization`;
* bridge/view: `CubicRegularizationBacktracking.IsNextRegularization`.
-/

namespace CubicRegularizationBacktracking

open RegularizedNewton

variable {f : X → ℝ} {stepMap : ℝ → X → X} {modelValue : ℝ → X → ℝ}
variable {x : ℕ → X} {regularization : ℕ → ℝ} {L0 L : ℝ} {N : ℕ}

/-- The initial interval condition `M₀ ∈ [L₀, 2L]` together with `L₀ > 0` already forces
`L > 0`. -/
theorem L_pos_of_regularization_zero_mem_Icc
    (hregularization_zero_mem_Icc : regularization 0 ∈ Set.Icc L0 (2 * L))
    (hL0 : 0 < L0) :
    0 < L := by
  have hM0_pos : 0 < regularization 0 :=
    lt_of_lt_of_le hL0 hregularization_zero_mem_Icc.1
  have hM0_le : regularization 0 ≤ 2 * L :=
    hregularization_zero_mem_Icc.2
  linarith

section AutomaticAcceptanceAboveL

variable
  (hautomatic :
    ∀ k : ℕ, k ≤ N → ∀ ⦃M : ℝ⦄,
      M ∈ Set.Ici L →
        M ∈ acceptingParameters f stepMap modelValue (x k))
  (hL0 : 0 < L0)

include hautomatic hL0

/-- If the current regularization parameter lies in `[L₀, 2L]`, then automatic acceptance above
`L` produces some accepted backtracking exponent at that step. -/
theorem acceptingExponents_nonempty_of_mem_Icc
    {k : ℕ} (hk : k ≤ N)
    (hk_regularization : regularization k ∈ Set.Icc L0 (2 * L)) :
    (acceptingExponents f stepMap modelValue (x k) (regularization k)).Nonempty := sorry

end AutomaticAcceptanceAboveL

section FiniteHorizon

variable
  (htrajectory :
    ∀ i : Fin (N + 1),
      IsNextRegularization
        f stepMap modelValue (x i.1) (regularization i.1) L0
        (regularization (i.1 + 1)))
  (hautomatic :
    ∀ k : ℕ, k ≤ N → ∀ ⦃M : ℝ⦄,
      M ∈ Set.Ici L →
        M ∈ acceptingParameters f stepMap modelValue (x k))
  (hregularization_zero_mem_Icc : regularization 0 ∈ Set.Icc L0 (2 * L))
  (hL0 : 0 < L0)

include htrajectory hautomatic hregularization_zero_mem_Icc hL0

-- Proof sketch: start from `hregularization_zero_mem_Icc`, derive accepted exponents from
-- `hautomatic`, and use `htrajectory` together with the minimality of the least
-- accepted exponent to show `hat M_k < 2L`; then `nextRegularization` keeps the next parameter
-- inside `[L₀, L] ⊆ [L₀, 2L]`.
/-- Under automatic acceptance above `L`, every regularization parameter produced by the canonical
conservative backtracking update up to index `N + 1` stays in the admissible interval
`[L₀, 2L]`. -/
theorem regularization_mem_Icc
    :
    ∀ k : ℕ, k ≤ N + 1 → regularization k ∈ Set.Icc L0 (2 * L) := sorry

/-- Every regularization parameter produced up to index `N + 1` stays bounded by `2L`. -/
theorem regularization_le_two_mul_L
    :
    ∀ k : ℕ, k ≤ N + 1 → regularization k ≤ 2 * L := by
  intro k hk
  exact (regularization_mem_Icc
    htrajectory hautomatic hregularization_zero_mem_Icc hL0 k hk).2

/-- Under the automatic-acceptance hypothesis, every step `k ≤ N` admits an accepted backtracking
exponent. -/
theorem acceptingExponents_nonempty
    {k : ℕ} (hk : k ≤ N) :
    (acceptingExponents f stepMap modelValue (x k) (regularization k)).Nonempty := by
  exact acceptingExponents_nonempty_of_mem_Icc
    hautomatic hL0 hk
    (regularization_mem_Icc
      htrajectory hautomatic hregularization_zero_mem_Icc hL0
      k (le_trans hk (Nat.le_succ N)))

/-- The total number of backtracking increments accumulated from steps `0` through `N`. -/
def totalBacktrackingIncrements
    :
    ℕ :=
  ∑ i : Fin (N + 1),
    index f stepMap modelValue (x i) (regularization i)
      (acceptingExponents_nonempty
        htrajectory hautomatic hregularization_zero_mem_Icc hL0
        (Nat.lt_succ_iff.mp i.2))

/-- The total number of evaluated trial mappings `T_M` over the first `N + 1` iterations equals
one trial per iteration plus the extra backtracking increments. -/
def totalComputedMappings
    :
    ℕ :=
  (N + 1) +
    totalBacktrackingIncrements
      htrajectory hautomatic hregularization_zero_mem_Icc hL0

-- Proof sketch: for each step `k`, the conservative update law gives
-- `2^(i_k - 1) M_k ≤ M_(k+1)`, so the least accepted exponent satisfies
-- `i_k ≤ 1 + log₂ (M_(k+1) / M_k)`. Summing these inequalities over `k = 0, …, N` telescopes the
-- logarithmic term to the endpoint ratio `M_(N+1) / M₀`.
/-- The total number of conservative backtracking increments is bounded by the number of
iterations plus the base-`2` logarithm of the endpoint regularization ratio. -/
theorem totalBacktrackingIncrements_le_numSteps_add_logb_endpoint_ratio
    :
    (totalBacktrackingIncrements
      htrajectory hautomatic hregularization_zero_mem_Icc hL0 : ℝ) ≤
      (N + 1 : ℝ) + Real.logb 2 (regularization (N + 1) / regularization 0) := sorry

-- Proof sketch: combine
-- `totalBacktrackingIncrements_le_numSteps_add_logb_endpoint_ratio` with the propagated interval
-- bounds `regularization 0 ≥ L₀` and `regularization (N + 1) ≤ 2L`.
/-- The total number of conservative backtracking increments is bounded by the number of
iterations plus `log₂ (2L / L₀)`. -/
theorem totalBacktrackingIncrements_le_numSteps_add_logb_double_ratio
    :
    (totalBacktrackingIncrements
      htrajectory hautomatic hregularization_zero_mem_Icc hL0 : ℝ) ≤
      (N + 1 : ℝ) + Real.logb 2 ((2 * L) / L0) := sorry

-- Proof sketch: by definition,
-- `totalComputedMappings = (N + 1) + totalBacktrackingIncrements`. Apply
-- `totalBacktrackingIncrements_le_numSteps_add_logb_double_ratio` and rearrange the constants.
/-- Proposition 4.1.16: for the conservative backtracking rule, if the acceptance inequality holds
for every tested parameter `M ≥ L` and the initial regularization satisfies `M₀ ∈ [L₀, 2L]`,
then the total number of computed trial mappings `T_M` through iteration `N` is at most
`2 (N + 1) + log₂ (2L / L₀)`. -/
theorem totalComputedMappings_le_conservative_backtracking_cost_bound
    :
    (totalComputedMappings
      htrajectory hautomatic hregularization_zero_mem_Icc hL0 : ℝ) ≤
      (2 : ℝ) * (N + 1 : ℝ) + Real.logb 2 ((2 * L) / L0) := sorry

end FiniteHorizon

end CubicRegularizationBacktracking
