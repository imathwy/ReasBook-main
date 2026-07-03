import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_7_13 (from Chap07) -/
noncomputable section

universe u

/- Definition 7.13 lies in the feasible-set / closed-ball localization domain.

Sampled owner-style declarations:
- mathlib `Metric.closedBall`
- mathlib `Metric.mem_closedBall`
- core `Set.inter`

Best owner abstraction:
- source-facing: `boundedFeasibleSet Q1 x0 ρ`, the textbook localized feasible set `Q₁(ρ)`
- core/canonical: `Q1 ∩ Metric.closedBall x0 ρ`
- bridge/view: membership lemmas in distance and norm form

Primitive data:
- a feasible set `Q1 : Set E`
- a base point `x0 : E`
- a radius `ρ : ℝ`

Derived API:
- membership as `x ∈ Q1 ∧ dist x x0 ≤ ρ`
- in normed additive groups, the equivalent norm form `x ∈ Q1 ∧ ‖x - x0‖ ≤ ρ`
-/

section Metric

variable {E : Type u} [PseudoMetricSpace E]

/-- Definition 7.13: for `ρ ≥ 0`, the bounded feasible set `Q₁(ρ)` is the subset of the feasible
set `Q₁` consisting of the points whose distance from `x₀` is at most `ρ`. -/
def boundedFeasibleSet (Q1 : Set E) (x0 : E) (ρ : ℝ) : Set E :=
  Q1 ∩ Metric.closedBall x0 ρ

/-- Membership in the bounded feasible set means ambient feasibility together with the distance
bound `dist x x₀ ≤ ρ`. -/
theorem mem_boundedFeasibleSet_iff_dist
    {Q1 : Set E} {x0 x : E} {ρ : ℝ} :
    x ∈ boundedFeasibleSet Q1 x0 ρ ↔ x ∈ Q1 ∧ dist x x0 ≤ ρ := by
  simp [boundedFeasibleSet]

end Metric

section Normed

variable {E : Type u} [SeminormedAddCommGroup E]

/-- Membership in the bounded feasible set means ambient feasibility together with the Euclidean
bound `‖x - x₀‖ ≤ ρ`. -/
theorem mem_boundedFeasibleSet_iff
    {Q1 : Set E} {x0 x : E} {ρ : ℝ} :
    x ∈ boundedFeasibleSet Q1 x0 ρ ↔ x ∈ Q1 ∧ ‖x - x0‖ ≤ ρ := by
  simpa [dist_eq_norm] using
    (mem_boundedFeasibleSet_iff_dist : x ∈ boundedFeasibleSet Q1 x0 ρ ↔ x ∈ Q1 ∧ dist x x0 ≤ ρ)

end Normed

/-! ### Lemma_7_13 (from Chap07) -/
open InnerProductSpace
open scoped Gradient HessianDualLocalNorm

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-
Lemma 7.13 lies in the Chapter 7 barrier-subgradient / self-concordant local-dual-norm domain.

Mandatory domain-style sampling before refinement:
- `IsSelfConcordantBarrierOnWith (interior Q) ν F` in `Chap05/Definition_5_3_2`, the Chapter 5
  owner for the barrier structure on the intrinsic strict feasible region;
- `dualLocalNorm` together with the determinant bridge `HessianDualLocalNorm.ofDetNeZero` in
  `Chap05/Definition_5_0_20`, the owner of the Hessian dual local norm and its determinant-based
  source-facing bridge;
- `IsSelfConcordantOnWith.hessian_isPositive` in `Chap05/Definition_5_1_1`, inherited from the
  barrier owner and supplying the local Hessian positivity needed by `dualLocalNorm`;
- mathlib `ConcaveOn`, the canonical owner for the concavity hypothesis on `interior Q`.

Best owner abstraction:
- source-facing: the dual-local-norm bound on `∇ ψ x` for a positive concave function on
  `interior Q`;
- core/canonical: `IsSelfConcordantBarrierOnWith (interior Q) ν F`, `ConcaveOn`, and
  `HessianDualLocalNorm.ofDetNeZero F x hPos hH g`;
- bridge/view: the supporting-hyperplane inequality for `ψ` along the inverse-Hessian direction.

Primitive data:
- the barrier owner on `interior Q`;
- the point `x ∈ interior Q`;
- the gradient witness for `ψ` at `x`;
- concavity and positivity of `ψ` on `interior Q`;
- Hessian nondegeneracy at `x`.

Derived API:
- local Hessian positivity at `x`, derived from the barrier owner;
- the dual local norm of the gradient covector, expressed through the Chapter 5 determinant
  bridge.

The previous statement kept both Hessian positivity and Hessian nondegeneracy as primitive public
inputs, even though positivity is already derived canonically from the barrier owner. This
refinement keeps the source-facing theorem, but moves it onto the chapter owner surface on
`interior Q` and leaves only the genuinely independent nondegeneracy witness explicit.
-/

-- Proof sketch: move from `x` in the inverse-Hessian direction of `∇ ψ x` by any local-norm
-- radius `r < 1`, use the self-concordant barrier inclusion to stay inside `interior Q`, apply
-- positivity of `ψ` at the new point, and then use the supporting-hyperplane inequality from
-- concavity together with the explicit choice of direction. Letting `r ↑ 1` yields the bound.
/-- Lemma 7.13: if `F` is a `ν`-self-concordant barrier on `interior Q` and `ψ` is a positive
concave function there, then at every interior point `x` where `ψ` has gradient `∇ ψ x`, the
dual local norm of that gradient with respect to the barrier Hessian of `F` is bounded by the
value `ψ x`. -/
theorem dualLocalNorm_gradient_le_value_of_concaveOn_pos
    {Q : Set E} {ν : NNReal} {F ψ : E → ℝ} {x : E}
    (hF : IsSelfConcordantBarrierOnWith (interior Q) ν F)
    (hx : x ∈ interior Q)
    (hgrad : HasGradientAt ψ (∇ ψ x) x)
    (hψ_concave : ConcaveOn ℝ (interior Q) ψ)
    (hψ_pos : ∀ ⦃y : E⦄, y ∈ interior Q → 0 < ψ y)
    (hH : (hessian F x).det ≠ 0) :
    let hPos := hF.toIsStandardSelfConcordantOn.hessian_isPositive hx
    HessianDualLocalNorm.ofDetNeZero F x hPos hH ((toDual ℝ E) (∇ ψ x)) ≤ ψ x := sorry

end

/-! ### Proposition_7_13 (from Chap07) -/
noncomputable section

universe u

variable {ι : Type u} [Fintype ι] [Nonempty ι]
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/- Proposition 7.13 lies in the chapter's finite max-absolute-linear / symmetric log-sum-exp
smoothing domain.

Sampled owner-style declarations:
- `maxTypeObjective` and `maxTypeObjective_apply` in `Chap02/Lemma_2_18`;
- `absLinearLogSumExp` and `absLinearLogSumExp_apply` in `Chap07/Proposition_7_14`;
- the same finite-max owner specialized to the absolute inner-product family.

Best owner abstraction:
- source-facing: Proposition 7.13's smoothing inequality for `x ↦ max_i |⟪a_i, x⟫|`;
- core/canonical: `maxTypeObjective (fun i x ↦ |⟪aᵢ, x⟫|)` and `absLinearLogSumExp μ a`;
- bridge/view: the source-facing bound below.

Primitive data:
- the finite family `a : ι → E`;
- the positive smoothing parameter `μ : {μ : ℝ // 0 < μ}`.

Derived API:
- the canonical unsmoothed owner `maxTypeObjective (fun i x ↦ |⟪aᵢ, x⟫|)`;
- the canonical smoothing owner `absLinearLogSumExp μ a`;
- the additive error term `μ log (2 * Fintype.card ι)`.

This refinement deletes the duplicate local wrappers `absoluteInnerMaxObjective` and
`maxAbsoluteInnerLogSumExpSmoothing`, and reuses the project owner `maxTypeObjective` directly
instead of a second Chapter 7 max-objective owner. -/

/-- Proposition 7.13: for a finite family `aᵢ` in a real inner product space and a positive
smoothing parameter `μ`, the symmetric smoothing of `x ↦ max_i |⟪a_i, x⟫|` lies between that max
and the same max plus `μ log (2 * Fintype.card ι)` at every point `x`. -/
-- Proof sketch: use `maxTypeObjective_apply`, specialized to the absolute inner-product family,
-- to identify the unsmoothed objective with
-- the finite maximum of the absolute pairings, and `absLinearLogSumExp_apply` together with
-- `absLinearLogSumExpOmega_eq` to expand the smoothing. For each `i`, compare
-- `exp (⟪aᵢ, x⟫ / μ) + exp (-⟪aᵢ, x⟫ / μ)` with `exp (|⟪aᵢ, x⟫| / μ)` from below and with
-- `2 * exp (|⟪aᵢ, x⟫| / μ)` from above, sum over `i`, and apply `μ * log`.
theorem maxTypeObjective_absInner_smoothing_bounds
    (a : ι → E) (μ : {μ : ℝ // 0 < μ}) (x : E) :
    maxTypeObjective (fun i y ↦ |inner ℝ (a i) y|) x ≤ absLinearLogSumExp μ a x ∧
      absLinearLogSumExp μ a x ≤
        maxTypeObjective (fun i y ↦ |inner ℝ (a i) y|) x +
          (μ : ℝ) * Real.log (2 * Fintype.card ι) := sorry

/-! ### Theorem_7_13 (from Chap07) -/
noncomputable section

universe u

open scoped ConstrainedArgmin

section

variable {E : Type u} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]

/- Theorem 7.13 lies in Chapter 7's barrier-regularized affine-maximization domain.

Mandatory domain-style sampling before refinement:
- `maximalValueOn` in `Chap07/Definition_7_56.lean`, the chapter owner for optimal values of real
  objectives on feasible sets;
- the direct specialization of `maximalValueOn` in `Chap07/Definition_7_55.lean` to the
  barrier-regularized affine payoff on `hatP ∩ interior Q`;
- `x0 ∈ argmin[hatP ∩ interior Q] F` in `Chap07/Definition_7_52.lean`, the chapter owner for the
  constrained analytic center appearing in the theorem hypotheses;
- `IsMaxOn`, the canonical owner for the attained maximizers of the unsmoothed and smoothed
  problems;
- `affineMax_le_affineBarrierRegularizedPayoff_max_add_logTerm` and
  `affineMax_sub_base_le_sq_sqrt_add_sqrt_of_affineBarrierRegularizedPayoff_max` in
  `Chap07/Lemma_7_11.lean`, the upstream witness-level comparisons whose attained-value forms are
  auxiliary to the owner-level scalar bridge;
- the nearby `.toReal` owner style in `Chap07/Proposition_7_23.lean`.

Best owner abstraction:
- source-facing: Theorem 7.13's comparison between the actual Chapter 7 optimal value
  `maximalValueOn (hatP ∩ Q) ℓ` and the barrier-regularized value
  `maximalValueOn (hatP ∩ interior Q) (affineBarrierRegularizedPayoff x0 β ℓ F)` under the
  constrained analytic-center, maximizer, and barrier-segment hypotheses;
- core/canonical: `maximalValueOn`, `argmin[hatP ∩ interior Q] F`, and `IsMaxOn`;
- bridge/view: the scalar logarithmic and square-gap inequalities on the real owner surfaces
  `ℓ⋆.toReal` and `ℓ⋆(β).toReal`.

Primitive data:
- the feasible sets `hatP` and `Q`;
- the barrier term `F`, base point `x₀`, and affine functional `ℓ`;
- the smoothing coefficient `β` and barrier parameter `v`;
- the attained maximizers `xStar` and `xBeta`.

Derived API:
- the actual optimal value `ℓ⋆` and the direct smoothed specialization `ℓ⋆β` of
  `maximalValueOn`;
- the `.toReal` bridge back to the textbook real inequalities;
- the auxiliary scalar gap-bound companion theorem below;
- the closed-form logarithmic comparison bound below.

Source/core/bridge triage:
- source-facing: the numbered theorem `optimal_value_le_smoothed_value_log_barrier_bound`;
- core/canonical: `maximalValueOn`, `argmin[hatP ∩ interior Q] F`, and `IsMaxOn`;
- bridge/view: the scalar logarithmic and square-gap comparison hypotheses on the attained values
  `ℓ xStar` and `Φβ xBeta`, together with the owner equalities supplied by
  `maximalValueOn_eq_of_isMaxOn`.

The previous version promoted the bridge/view layer to the main labeled theorem by assuming the
already-derived scalar gap inequalities as hypotheses on `ℓ⋆.toReal` and `ℓ⋆(β).toReal`, which
does not faithfully encode finiteness in `EReal`. This refinement restores the numbered theorem to
the source-facing layer, with the actual Chapter 7 constrained-center, maximizer, and
barrier-segment hypotheses, and demotes the scalar-gap formulation to a companion theorem stated
on attained real values and lifted back to the owner values by `maximalValueOn_eq_of_isMaxOn`.
-/

variable {hatP Q : Set E} {F : E → ℝ} {x0 xStar xBeta : E}
variable {ℓ : AffineMap ℝ E ℝ} {β v : ℝ}

/- Fixed ambient-context notation for the Chapter 7 optimal value owner `ℓ⋆`. -/
set_option quotPrecheck false in
local notation:max "ℓ⋆" =>
  maximalValueOn (hatP ∩ Q) ℓ

local notation "P₀" => hatP ∩ interior Q
local notation "Φβ" => affineBarrierRegularizedPayoff x0 β ℓ F
set_option quotPrecheck false in
local notation:max "ℓ⋆β" =>
  maximalValueOn P₀ Φβ

-- Proof sketch: use `maximalValueOn_eq_of_isMaxOn` to identify the owner values `ℓ⋆` and `ℓ⋆(β)`
-- with the attained real values `ℓ xStar` and `Φβ xBeta`. Combining the logarithmic comparison on
-- those attained values with the square-gap bound yields the displayed owner-level estimate.
/-- If `xStar` and `xBeta` attain the unsmoothed and smoothed maxima and their attained values
satisfy the logarithmic and square-gap comparisons produced by the Chapter 7 source hypotheses,
then the actual owner value `ℓ⋆` is bounded above by the smoothed owner value `ℓ⋆(β)` plus the
explicit logarithmic error term. This is the bridge/view form of Theorem 7.13, kept as an
auxiliary companion. -/
theorem optimal_value_le_smoothed_value_log_barrier_bound_of_gap_bounds
    (hβv : 0 < β * v)
    (hxStar_mem : xStar ∈ hatP ∩ Q)
    (hxStar_max : IsMaxOn ℓ (hatP ∩ Q) xStar)
    (hxBeta_mem : xBeta ∈ P₀)
    (hxBeta_max : IsMaxOn Φβ P₀ xBeta)
    (hlogGap :
      ℓ xStar ≤
        Φβ xBeta +
          β * v * (1 + max (Real.log ((ℓ xStar - ℓ x0) / (β * v))) 0))
    (hsquareGap :
      ℓ xStar - ℓ x0 ≤
        (Real.sqrt (Φβ xBeta - ℓ x0) + Real.sqrt (β * v)) ^ (2 : ℕ)) :
    ℓ⋆ ≤
      ℓ⋆β +
        β * v *
          (1 + 2 * Real.log
            (1 + Real.sqrt (((ℓ⋆β).toReal - ℓ x0) / (β * v)))) := sorry

-- Proof sketch: the constrained analytic-center hypothesis for `x₀`, the attained maximizers
-- `xStar` and `xBeta`, and the barrier segment estimate first yield the attained-value
-- inequalities from Lemma 7.11. Applying the companion bridge theorem above lifts those
-- inequalities to the owner values `ℓ⋆` and `ℓ⋆(β)` and gives the displayed bound.
/-- Theorem 7.13: if `x₀` is a constrained analytic center of the strict feasible region
`hatP ∩ interior Q`, if `xStar` maximizes `ℓ` on `hatP ∩ Q`, if `xBeta` maximizes the
barrier-regularized payoff on `hatP ∩ interior Q`, and if every open segment from `x₀` to a
feasible point of `hatP ∩ Q` stays in the strict feasible region and satisfies the displayed
barrier estimate, then the actual optimal value `ℓ⋆` is bounded above by the smoothed value
`ℓ⋆(β)` plus the explicit logarithmic error term. -/
theorem optimal_value_le_smoothed_value_log_barrier_bound
    (hβ : 0 < β) (hv : 0 < v)
    (hx0 : x0 ∈ argmin[P₀] F)
    (hxStar_mem : xStar ∈ hatP ∩ Q)
    (hxStar_max : IsMaxOn ℓ (hatP ∩ Q) xStar)
    (hxBeta_mem : xBeta ∈ P₀)
    (hxBeta_max : IsMaxOn Φβ P₀ xBeta)
    (hsegment_mem :
      ∀ ⦃x : E⦄, x ∈ hatP ∩ Q → ∀ ⦃α : ℝ⦄, α ∈ Set.Ico (0 : ℝ) 1 →
        x0 + α • (x - x0) ∈ P₀)
    (hF_segment :
      ∀ ⦃x : E⦄, x ∈ hatP ∩ Q → ∀ ⦃α : ℝ⦄, α ∈ Set.Ico (0 : ℝ) 1 →
        F (x0 + α • (x - x0)) ≤ F x0 - v * Real.log (1 - α)) :
    ℓ⋆ ≤
      ℓ⋆β +
        β * v *
          (1 + 2 * Real.log
            (1 + Real.sqrt (((ℓ⋆β).toReal - ℓ x0) / (β * v)))) := sorry

end
