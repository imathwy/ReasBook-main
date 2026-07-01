import Nesterov.Chap06.Lemma_6_12

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped BigOperators

universe u v

variable {E₁ : Type u} {E₂ : Type v}

/- Theorem 6.3 lies in the Chapter 6 smoothing / primal-dual gap domain.

Sampled owner-style declarations:
- `Finset.centerMass` and `Finset.centerMass_eq_of_sum_1`, the canonical owners for a finite
  normalized weighted average and its finite-sum expansion;
- `primal_dual_gap_bound_of_smoothed_lower_approximation` in `Lemma_6_12`, the chapter owner for
  recording a raw primal-dual gap bound canonically as interval membership in `Set.Icc`;
- `scaled_smoothing_parameter_product_eq` in `Proposition_6_28`, the chapter's algebraic owner for
  simplifying the optimized smoothing-parameter substitution.

Best owner abstraction:
- source-facing: Theorem 6.3's explicit weight family, weighted dual iterate `\hat u_N`, and
  optimized smoothing parameter `μ(N)`;
- core/canonical: `Finset.centerMass` for `\hat u_N` and raw interval membership
  `f x_N - φ(\hat u_N) ∈ Set.Icc 0 bound` for the primal-dual gap;
- bridge/view: the explicit coefficient formula
  `2 (i + 1) / ((N + 1) (N + 2))` for the weight family.

Primitive data:
- the explicit finite weight family on `Fin (N + 1)`;
- the chosen smoothing parameter `μ(N)` at a positive iteration count `N`;
- the smoothed objective value `fμ x_N` together with its pointwise lower-approximation at `x_N`
  and residual-gap bounds.

Derived API:
- the normalized weighted-average realization of `\hat u_N` through `Finset.centerMass`;
- the source finite-sum expansion of that weighted average;
- the canonical interval-valued gap bounds.

Source/core/bridge triage:
- source-facing: the explicit model weights, the weighted dual iterate `\hat u_N`, and the
  optimized Theorem 6.3 gap estimate;
- core/canonical: `Finset.centerMass` and `Set.Icc`;
- bridge/view: the explicit coefficient formula and finite-sum expansion.

The previous version kept parallel local public wrappers for the averaged dual iterate and the raw
gap. This refinement deletes those wrappers, reuses the chapter's weighted-average owner directly,
and restores Theorem 6.3 as a source-facing smoothing statement rather than an algebraic
post-processing lemma on an already packaged raw gap bound. -/

/-- The weight family
`a_i^(N) = 2 (i + 1) / ((N + 1) (N + 2))`
used in the weighted dual iterate `\hat u_N` of Theorem 6.3. -/
def explicitModelDualAverageWeights (N : ℕ) : Fin (N + 1) → ℝ :=
  fun i ↦ (2 * (((i : ℕ) : ℝ) + 1)) / (((N : ℝ) + 1) * ((N : ℝ) + 2))

-- Proof sketch: unfold `explicitModelDualAverageWeights`.
/-- Evaluating `explicitModelDualAverageWeights N` at `i` recovers the textbook coefficient
`2 (i + 1) / ((N + 1) (N + 2))`. -/
theorem explicitModelDualAverageWeights_apply (N : ℕ) (i : Fin (N + 1)) :
    explicitModelDualAverageWeights N i =
      (2 * (((i : ℕ) : ℝ) + 1)) / (((N : ℝ) + 1) * ((N : ℝ) + 2)) :=
  rfl

-- Proof sketch: sum the arithmetic progression `1 + 2 + ··· + (N + 1)` and divide by
-- `((N + 1) (N + 2)) / 2`.
/-- The explicit-model weights form a normalized weight family. -/
theorem explicitModelDualAverageWeights_sum_eq_one (N : ℕ) :
    ∑ i, explicitModelDualAverageWeights N i = 1 := by
  sorry

-- Proof sketch: apply `Finset.centerMass_eq_of_sum_1` and use
-- `explicitModelDualAverageWeights_sum_eq_one`.
/-- The center of mass with `explicitModelDualAverageWeights N` is the source finite sum
`\hat u_N = Σ_{i=0}^N 2 (i + 1) / ((N + 1) (N + 2)) u_i`. -/
theorem centerMass_explicitModelDualAverageWeights_eq_sum
    [AddCommGroup E₂] [Module ℝ E₂]
    (N : ℕ) (u : Fin (N + 1) → E₂) :
    Finset.univ.centerMass (explicitModelDualAverageWeights N) u =
      ∑ i, explicitModelDualAverageWeights N i • u i := by
  simpa using
    (Finset.univ.centerMass_eq_of_sum_1 u (explicitModelDualAverageWeights_sum_eq_one N))

section ExplicitModelSmoothing

variable [NormedAddCommGroup E₁] [NormedSpace ℝ E₁]
  [NormedAddCommGroup E₂] [NormedSpace ℝ E₂]

/-- The smoothing parameter
`μ(N) = 2 ‖A‖ / √(N (N + 1)) * √(D₁ / D₂)`
chosen in Theorem 6.3. -/
def explicitModelSmoothingParameter
    (A : E₁ →L[ℝ] StrongDual ℝ E₂) (D₁ D₂ : ℝ) (N : ℕ+) : ℝ :=
  (2 * ‖A‖ / Real.sqrt ((N : ℝ) * ((N : ℝ) + 1))) * Real.sqrt (D₁ / D₂)

-- Proof sketch: unfold `explicitModelSmoothingParameter`.
/-- Evaluating `explicitModelSmoothingParameter` recovers the displayed formula for `μ(N)`. -/
theorem explicitModelSmoothingParameter_def
    (A : E₁ →L[ℝ] StrongDual ℝ E₂) (D₁ D₂ : ℝ) (N : ℕ+) :
    explicitModelSmoothingParameter A D₁ D₂ N =
      (2 * ‖A‖ / Real.sqrt ((N : ℝ) * ((N : ℝ) + 1))) * Real.sqrt (D₁ / D₂) :=
  rfl

-- Proof sketch: write
-- `f x_N - φ(\hat u_N) = (f x_N - fμ x_N) + (fμ x_N - φ(\hat u_N))`.
-- The smoothing lower-approximation bounds the first term by `μ(N) D₂`, while the source
-- residual hypothesis bounds the second term. The lower bound comes from
-- `φ(\hat u_N) ≤ fμ x_N ≤ f x_N`.
/-- Companion source-facing bridge for Theorem 6.3: if the smoothed value `fμ x_N` lies between
`φ(\hat u_N)` and `f x_N`, if the lower smoothing estimate at `x_N` has error at most `μ(N) D₂`,
and if the residual smoothed gap is bounded by the model term
`4 ‖A‖² D₁ / (μ(N) N (N + 1)) + 4 M D₁ / (N (N + 1))`, then the raw primal-dual gap at
`(x_N, \hat u_N)` lies in the interval
`[0, μ(N) D₂ + 4 ‖A‖² D₁ / (μ(N) N (N + 1)) + 4 M D₁ / (N (N + 1))]`. -/
theorem explicitModelPrimalDualGap_mem_Icc_of_smoothed_gap_bound
    (A : E₁ →L[ℝ] StrongDual ℝ E₂) (f fμ : E₁ → ℝ) (φ : E₂ → ℝ)
    (N : ℕ+) (xN : E₁) (u : Fin ((N : ℕ) + 1) → E₂)
    (D₁ D₂ M : ℝ)
    (hxN_approx :
      fμ xN ≥ f xN - explicitModelSmoothingParameter A D₁ D₂ N * D₂)
    (hφ_le : φ (Finset.univ.centerMass (explicitModelDualAverageWeights N) u) ≤ fμ xN)
    (hfμ_le : fμ xN ≤ f xN)
    (hsmoothed_gap :
      fμ xN - φ (Finset.univ.centerMass (explicitModelDualAverageWeights N) u) ≤
        (4 * ‖A‖ ^ (2 : ℕ) * D₁) /
            (explicitModelSmoothingParameter A D₁ D₂ N * ((N : ℝ) * ((N : ℝ) + 1))) +
          (4 * M * D₁) / ((N : ℝ) * ((N : ℝ) + 1))) :
    f xN - φ (Finset.univ.centerMass (explicitModelDualAverageWeights N) u) ∈ Set.Icc 0
      (explicitModelSmoothingParameter A D₁ D₂ N * D₂ +
        (4 * ‖A‖ ^ (2 : ℕ) * D₁) /
            (explicitModelSmoothingParameter A D₁ D₂ N * ((N : ℝ) * ((N : ℝ) + 1))) +
        (4 * M * D₁) / ((N : ℝ) * ((N : ℝ) + 1))) := by
  sorry

-- Proof sketch: first apply `explicitModelPrimalDualGap_mem_Icc_of_smoothed_gap_bound`.
-- Then substitute the explicit choice of `μ(N)` and simplify the first two upper-bound terms to
-- `4 ‖A‖ √(D₁ D₂) / √(N (N + 1))`, using the chapter's algebraic owner
-- `scaled_smoothing_parameter_product_eq`.
/-- Theorem 6.3: let
`μ(N) = 2 ‖A‖ / √(N (N + 1)) * √(D₁ / D₂)` and
`\hat u_N = Finset.univ.centerMass (explicitModelDualAverageWeights N) u`.
If `φ(\hat u_N) ≤ fμ x_N ≤ f x_N`, if `fμ` is a lower smoothing of `f` with error at most
`μ(N) D₂` at `x_N`, and if the smoothed residual gap at `(x_N, \hat u_N)` is bounded by
`4 ‖A‖² D₁ / (μ(N) N (N + 1)) + 4 M D₁ / (N (N + 1))`,
then
`0 ≤ f(x_N) - φ(\hat u_N) ≤ 4 ‖A‖ √(D₁ D₂) / √(N (N + 1)) + 4 M D₁ / (N (N + 1))`. -/
theorem optimized_primal_dual_gap_bound_for_explicit_model_smoothing
    (A : E₁ →L[ℝ] StrongDual ℝ E₂) (f fμ : E₁ → ℝ) (φ : E₂ → ℝ)
    (N : ℕ+) (xN : E₁) (u : Fin ((N : ℕ) + 1) → E₂)
    (D₁ D₂ M : ℝ) (hD₁ : 0 ≤ D₁) (hD₂ : 0 < D₂)
    (hxN_approx :
      fμ xN ≥ f xN - explicitModelSmoothingParameter A D₁ D₂ N * D₂)
    (hφ_le : φ (Finset.univ.centerMass (explicitModelDualAverageWeights N) u) ≤ fμ xN)
    (hfμ_le : fμ xN ≤ f xN)
    (hsmoothed_gap :
      fμ xN - φ (Finset.univ.centerMass (explicitModelDualAverageWeights N) u) ≤
        (4 * ‖A‖ ^ (2 : ℕ) * D₁) /
            (explicitModelSmoothingParameter A D₁ D₂ N * ((N : ℝ) * ((N : ℝ) + 1))) +
          (4 * M * D₁) / ((N : ℝ) * ((N : ℝ) + 1))) :
    f xN - φ (Finset.univ.centerMass (explicitModelDualAverageWeights N) u) ∈ Set.Icc 0
      ((4 * ‖A‖ / Real.sqrt ((N : ℝ) * ((N : ℝ) + 1))) * Real.sqrt (D₁ * D₂) +
        (4 * M * D₁) / ((N : ℝ) * ((N : ℝ) + 1))) := by
  sorry

-- Proof sketch: combine the optimized interval bound with the hypothesis
-- `4 ‖A‖ √(D₁ D₂) / ε + 2 √(M D₁ / ε) ≤ N`, then check that the right-hand side of the bound is
-- at most `ε`.
/-- If the iteration count dominates the Theorem 6.3 complexity expression, then the weighted
dual iterate `\hat u_N` and the primal iterate `x_N` form an `ε`-accurate primal-dual pair. -/
theorem primal_dual_gap_le_epsilon_of_iteration_bound
    (A : E₁ →L[ℝ] StrongDual ℝ E₂) (f : E₁ → ℝ) (φ : E₂ → ℝ)
    (N : ℕ+) (xN : E₁) (u : Fin ((N : ℕ) + 1) → E₂)
    (D₁ D₂ M ε : ℝ) (hε : 0 < ε)
    (hgap :
      f xN - φ (Finset.univ.centerMass (explicitModelDualAverageWeights N) u) ∈ Set.Icc 0
        ((4 * ‖A‖ / Real.sqrt ((N : ℝ) * ((N : ℝ) + 1))) * Real.sqrt (D₁ * D₂) +
          (4 * M * D₁) / ((N : ℝ) * ((N : ℝ) + 1))))
    (hiter :
      (4 * ‖A‖ * Real.sqrt (D₁ * D₂)) / ε + 2 * Real.sqrt (M * D₁ / ε) ≤ (N : ℝ)) :
    f xN - φ (Finset.univ.centerMass (explicitModelDualAverageWeights N) u) ≤ ε := by
  sorry

end ExplicitModelSmoothing

end
