import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_3_34 (from Chap03) -/
noncomputable section

universe u

variable {E : Type u}

/- Definition 3.34 lies in the chapter's nonsmooth first-order black-box complexity domain.

Sampled owner-style declarations:
* `IsInLipschitzConvexProblemClass` in `Theorem_3_2_1`, the source-facing owner predicate for the
  class `𝒫(x₀, R, M)`;
* `IsMinOn f Set.univ xStar` in mathlib, the canonical owner of the chosen minimizer data for an
  unconstrained objective;
* `SetConstrainedMinimizationProblem.unconstrained f` in `Chap01/Definition_1_3_3`, the canonical
  Chapter 1 whole-space owner for the same objective;
* `SetConstrainedMinimizationProblem.unconstrained_isApproximateMinimizer_iff_sub_le` in
  `Chap02/Definition_2_8`, the canonical owner bridge from the whole-space approximate-minimizer
  predicate to the textbook objective-gap inequality.

Best owner abstraction:
* source-facing: the textbook `ε`-approximate-solution notion for an objective in `𝒫(x₀, R, M)`,
  expressed directly as the objective-gap predicate relative to a chosen minimizer `xStar`;
* core/canonical: `SetConstrainedMinimizationProblem.unconstrained f` together with
  `IsMinOn f Set.univ xStar`;
* bridge/view:
  `SetConstrainedMinimizationProblem.unconstrained_isApproximateMinimizer_iff_sub_le`.

Primitive data:
* the objective `f : E → ℝ`;
* the chosen minimizer `xStar : E`.

Derived API:
* the source-facing predicate `IsApproximateSolution f xStar ε xBar`;
* the bridge equating `IsApproximateSolution` with the Chapter 1 approximate-minimizer predicate
  for `SetConstrainedMinimizationProblem.unconstrained f`.

This file therefore removes the old bundled-problem wrapper surface. Definition 3.34 is stated
directly on `f` and `xStar`, while the whole-space Chapter 1 owner remains only a thin bridge
proved from `IsMinOn`.
-/

/-- Definition 3.34: relative to a chosen minimizer `x*`, a point `x̄` is an `ε`-approximate
solution of the unconstrained objective `f` when its objective gap above `f(x*)` is at most
`ε`. -/
def IsApproximateSolution (f : E → ℝ) (xStar : E) (ε : ℝ) (xBar : E) : Prop :=
  f xBar - f xStar ≤ ε

variable {f : E → ℝ} {xStar xBar : E}

/-- If `x*` globally minimizes `f`, then the source-facing approximate-solution predicate is
exactly the Chapter 1 approximate-minimizer predicate for the ambient whole-space owner. -/
theorem isApproximateSolution_iff_isApproximateMinimizer
    (hxStar : IsMinOn f Set.univ xStar) (ε : ℝ) (xBar : E) :
    IsApproximateSolution f xStar ε xBar ↔
      (SetConstrainedMinimizationProblem.unconstrained f).IsApproximateMinimizer ε xBar := by
  simpa [IsApproximateSolution] using
    (SetConstrainedMinimizationProblem.unconstrained_isApproximateMinimizer_iff_sub_le
      f hxStar ε).symm

theorem isApproximateSolution_iff_isApproximateMinimizer_nnreal
    (hxStar : IsMinOn f Set.univ xStar) (ε : NNReal) (xBar : E) :
    IsApproximateSolution f xStar ε xBar ↔
      (SetConstrainedMinimizationProblem.unconstrained f).IsApproximateMinimizer ε xBar := by
  simpa using isApproximateSolution_iff_isApproximateMinimizer hxStar (ε : ℝ) xBar

end

/-! ### Lemma_3_34 (from Chap03) -/
noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/- Lemma 3.34 is a source-facing one-step cutting-plane bound in the chapter's level-method
domain on a real inner-product space.

Sampled owner declarations:
- `LevelMethodHistory.levelValue_eq_optimal_sub_one_sub_alpha_mul_gap` in `Lemma_3_3_1`
- `nonsmoothModel` in `Lemma_3_3_2`
- `nonsmoothModel_apply` in `Lemma_3_3_2`
- `step_norm_lower_bound_of_level_method_assumptions` in `Lemma_3_3_2`

Best owner abstraction:
- the chapter owner theorem
  `step_norm_lower_bound_of_level_method_assumptions`
- the source-facing one-step model value as the `k = 0` evaluation of `nonsmoothModel`

Primitive data:
- the one-step points `x_k`, `x_{k+1}` and chosen subgradient `g_k`
- the scalars `f_k^*`, `δ_k`, `α`, and `M_f`
- the local bound `‖g_k‖ ≤ M_f`
- the one-step cutting-plane inequality
  `f(x_k) + ⟪g_k, x_{k+1} - x_k⟫ ≤ f_k^* - (1 - α) δ_k`

Derived API:
- the step-length lower bound below, obtained by viewing the current scalars as the `k = 0`
  instance of a `LevelMethodHistory` and the current affine minorant as the `k = 0` instance of
  the owner sampled model

Source/core/bridge triage:
- source-facing: the one-step cutting-plane inequality and its resulting step estimate
- core/canonical: `step_norm_lower_bound_of_level_method_assumptions`
- bridge/view: the constant history/model specialization at `k = 0`

This file keeps the source-facing cutting-plane inequality directly instead of introducing an
auxiliary scalar witness for the model value at `x_{k+1}`: that witness is exactly the `k = 0`
evaluation of `nonsmoothModel` and disappears after composing the two inequalities. The argument
only uses the real inner-product-space structure already required by the owner declarations, so
this file keeps that canonical ambient generality instead of re-specializing to `ℝ^n`. -/
/-- Lemma 3.34: if the one-step affine cut generated by `g_k` satisfies
`f(x_k) + ⟪g_k, x_{k+1} - x_k⟫ ≤ f_k^* - (1 - α) δ_k`, if `‖g_k‖ ≤ M_f`, and if
`f_k^* ≤ f(x_k)`, then the step length satisfies
`‖x_{k+1} - x_k‖ ≥ ((1 - α) δ_k) / M_f`. -/
-- Proof sketch: combine `f_k^* ≤ f x_k` with the cutting-plane inequality to obtain
-- `(1 - α) * δ_k ≤ -⟪g_k, x_{k+1} - x_k⟫`. Then apply Cauchy-Schwarz and the uniform bound
-- `‖g_k‖ ≤ M_f`, and divide by `M_f > 0`.
theorem step_norm_lower_bound_of_level_method_cutting_plane_bound
    {f : E → ℝ} {xk xNext gk : E} {α δk fkStar Mf : ℝ}
    (hMf_pos : 0 < Mf)
    (hgk_bound : ‖gk‖ ≤ Mf)
    (hcutting_plane :
      f xk + inner ℝ gk (xNext - xk) ≤ fkStar - (1 - α) * δk)
    (hfkStar_le : fkStar ≤ f xk) :
    ‖xNext - xk‖ ≥ ((1 - α) * δk) / Mf := by
  let history : LevelMethodHistory :=
    { approximateOptimalValue := fun _ ↦ fkStar - δk
      optimalValue := fun _ ↦ fkStar }
  let X : ℕ → E
    | 0 => xk
    | _ + 1 => xNext
  let g : ℕ → E := fun _ ↦ gk
  have hrecord_le_current : history.optimalValue 0 ≤ f (X 0) := by
    simpa [history, X] using hfkStar_le
  have hbound : ‖g 0‖ ≤ Mf := by
    simpa [g] using hgk_bound
  have hlevel_ge_model :
      history.levelValue α 0 ≥
        nonsmoothModel f X g 0 (X 1) := by
    rw [history.levelValue_eq_optimal_sub_one_sub_alpha_mul_gap α 0]
    simp [LevelMethodHistory.gap, history]
    simpa [X, g] using hcutting_plane
  have hstep :
      ‖X (0 + 1) - X 0‖ ≥
        ((1 - α) * history.gap 0) / Mf :=
    step_norm_lower_bound_of_level_method_assumptions
      α Mf hrecord_le_current hlevel_ge_model hbound hMf_pos
  simpa [LevelMethodHistory.gap, history, X] using hstep

end

/-! ### Proposition_3_34 (from Chap03) -/
noncomputable section

universe u

open scoped PointwiseGrowthFunction

/- Proposition 3.34 lies in the chapter's pointwise-growth / local-modulus domain.

Primary mathematical domain:
- supremal growth profiles of a real-valued function around a base point on a metric space.

Sampled owner-style declarations:
- `pointwiseGrowthFunction` in `Lemma_3_2_1`, the chapter owner for `ω_f(xBar; t)`;
- `pointwiseGrowthFunction_eq_zero_of_neg` in `Lemma_3_2_1`, the owner negative-radius
  simplification;
- `sub_le_pointwiseGrowthFunction_of_localizationMeasure` in `Lemma_3_2_1`, the first comparison
  theorem derived from the same owner;
- `bestFunctionValueGapUpTo_le_modulusAtBestRadius` in `Lemma_3_2_2`, a downstream theorem that
  consumes a monotone modulus owner directly.

Best owner abstraction:
- `pointwiseGrowthFunction`

Primitive data:
- a real-valued function `f : X → ℝ`;
- a base point `xBar : X`;
- a radius parameter `t : ℝ`.

Derived API:
- the nonpositive-radius vanishing formula;
- monotonicity in the radius parameter;
- the pointwise increment bound at radius `dist x xBar`.

Source/core/bridge triage:
- source-facing: Proposition 3.34's three elementary facts about the textbook growth profile
  `ω_f(xBar; t)`;
- core/canonical: `pointwiseGrowthFunction`;
- bridge/view: the radius-zero simplification and the closed-ball membership
  `x ∈ Metric.closedBall xBar (dist x xBar)`.

This file stays at the derived-API layer over the owner `pointwiseGrowthFunction`. The previous
pipeline stub already had the correct owner-facing statement shapes, so the refinement is to prove
those consequences directly from the owner definition rather than introducing any parallel local
modulus wrapper.
-/

section

variable {X : Type u} [MetricSpace X]

/-- Proposition 3.34 (1): the pointwise growth function `ω_f(xBar; t)` vanishes for every
nonpositive radius `t`. -/
-- Proof sketch: if `t < 0`, this is exactly the negative-radius clause in the definition of
-- `pointwiseGrowthFunction`. If `t = 0`, the closed ball of radius `0` is `{xBar}`, so the
-- defining supremum is the singleton value `f xBar - f xBar = 0`.
theorem pointwiseGrowthFunction_eq_zero_of_nonpos
    (f : X → ℝ) (xBar : X) (t : ℝ) (ht : t ≤ 0) :
    ω[f; xBar] t = 0 := by
  by_cases hneg : t < 0
  · exact pointwiseGrowthFunction_eq_zero_of_neg hneg
  · have ht0 : t = 0 := le_antisymm ht (le_of_not_gt hneg)
    subst ht0
    simp [pointwiseGrowthFunction]

/-- Proposition 3.34 (2): the function `t ↦ ω_f(xBar; t)` is monotone nondecreasing in the
radius parameter. -/
-- Proof sketch: for `t₁ ≤ t₂`, the closed ball `Metric.closedBall xBar t₁` is contained in
-- `Metric.closedBall xBar t₂`, so taking the supremum of `f y - f xBar` over the larger set can
-- only increase the value. The nonpositive-radius case is handled by the previous zero formula.
theorem pointwiseGrowthFunction_monotone
    (f : X → ℝ) (xBar : X) :
    Monotone (ω[f; xBar]) := by
  let S : ℝ → Set (WithTop ℝ) :=
    fun t ↦ (fun y : X ↦ ((f y - f xBar : ℝ) : WithTop ℝ)) '' Metric.closedBall xBar t
  intro t₁ t₂ ht
  by_cases ht₁_nonneg : 0 ≤ t₁
  · have ht₂_nonneg : 0 ≤ t₂ := le_trans ht₁_nonneg ht
    rw [pointwiseGrowthFunction, if_pos ht₁_nonneg, pointwiseGrowthFunction, if_pos ht₂_nonneg]
    change sSup (S t₁) ≤ sSup (S t₂)
    refine csSup_le_csSup ?_ ?_ ?_
    · exact ⟨⊤, fun _ _ ↦ le_top⟩
    · refine ⟨0, ?_⟩
      simpa [S] using Set.mem_image_of_mem
        (fun y : X ↦ ((f y - f xBar : ℝ) : WithTop ℝ))
        (Metric.mem_closedBall_self ht₁_nonneg)
    · rintro _ ⟨y, hy, rfl⟩
      exact Set.mem_image_of_mem _ (Metric.closedBall_subset_closedBall ht hy)
  · rw [pointwiseGrowthFunction_eq_zero_of_nonpos f xBar t₁ (le_of_not_ge ht₁_nonneg)]
    by_cases ht₂_nonneg : 0 ≤ t₂
    · rw [pointwiseGrowthFunction, if_pos ht₂_nonneg]
      have hzero_mem : (0 : WithTop ℝ) ∈ S t₂ := by
        simpa [S] using Set.mem_image_of_mem
          (fun y : X ↦ ((f y - f xBar : ℝ) : WithTop ℝ))
          (Metric.mem_closedBall_self ht₂_nonneg)
      exact le_csSup ⟨⊤, fun _ _ ↦ le_top⟩ hzero_mem
    · rw [pointwiseGrowthFunction_eq_zero_of_nonpos f xBar t₂ (le_of_not_ge ht₂_nonneg)]

/-- Proposition 3.34 (3): every increment `f x - f xBar` is bounded above by the pointwise growth
function evaluated at the distance from `x` to `xBar`. -/
-- Proof sketch: with `t = dist x xBar`, the point `x` belongs to `Metric.closedBall xBar t`, so
-- the defining supremum of `pointwiseGrowthFunction f xBar t` is at least the value
-- `f x - f xBar`.
theorem sub_le_pointwiseGrowthFunction_dist
    (f : X → ℝ) (xBar x : X) :
    f x - f xBar ≤ ω[f; xBar] (dist x xBar) := by
  rw [pointwiseGrowthFunction, if_pos dist_nonneg]
  have hx : x ∈ Metric.closedBall xBar (dist x xBar) := by
    simp [Metric.mem_closedBall]
  exact
    le_csSup
      ⟨⊤, fun _ _ ↦ le_top⟩
      (Set.mem_image_of_mem
        (fun y : X ↦ ((f y - f xBar : ℝ) : WithTop ℝ))
        hx)

end

/-! ### Theorem_3_34 (from Chap03) -/
/- Theorem 3.34 lies in the chapter's equality-constrained convex optimality domain.

Sampled owner declarations in this domain:
- `linearEqualityFeasibleSet` in `LinearEqualityFeasibleSet`, the chapter owner of the feasible
  set cut out by `x ∈ Q` and `A x = b`
- `dom` and `withTopRealPart` in `Definition_3_3`, the chapter owners for the effective domain
  and finite-value representative of an `ℝ ∪ {+∞}`-valued objective
- `subdifferential` and the notation `∂ f(x)` in `Definition_3_1_5`, the chapter owners for
  extended-valued subgradients
- `isMinOn_linearEqualityFeasibleSet_iff_exists_subgradient_multiplier_with_bound` in
  `Theorem_3_1_27`, the intrinsic linear-map optimality criterion already carrying the exact
  mathematical content needed here
- the real-valued constrained-subdifferential surface `g ∈ ∂[Q] f(x)` in `Theorem_3_44`, the later
  chapter notation for relative subgradients

Best owner abstraction:
- core/canonical:
  `isMinOn_linearEqualityFeasibleSet_iff_exists_subgradient_multiplier_with_bound`

Primitive data:
- a feasible set `Q`
- an extended-real-valued convex objective `f`
- a linear map `A`
- a right-hand side `b`
- a Slater point `xBar` with a feasible ball `Metric.ball xBar ε ⊆ Q`

Derived API:
- the feasibility conclusion `A xStar = b`
- a multiplier/subgradient witness with `gStar ∈ ∂ f(xStar)`
- the adjoint-norm bound coming from the Slater-ball value gap

Source/core/bridge triage:
- source-facing: the textbook matrix presentation with `Aᵀ` and a relative subgradient on `Q`
- core/canonical: the intrinsic linear-map theorem from `Theorem_3_1_27`
- bridge/view: the matrix specialization `A := A.toEuclideanLin` together with the transpose /
  adjoint identification and the real-valued relative-subgradient notation

The previous version duplicated the owner theorem at the coordinate `Matrix` / `EuclideanSpace`
level. This file now keeps Theorem 3.34 as a direct recall of the intrinsic chapter owner; the
textbook `Aᵀ` specialization is a downstream bridge/view, not a second public owner theorem.
-/

/- Theorem 3.34 is the intrinsic linear-map theorem
`isMinOn_linearEqualityFeasibleSet_iff_exists_subgradient_multiplier_with_bound`; the textbook
matrix form is the downstream specialization via `A.toEuclideanLin` and the standard
transpose/adjoint identification. -/
recall isMinOn_linearEqualityFeasibleSet_iff_exists_subgradient_multiplier_with_bound
