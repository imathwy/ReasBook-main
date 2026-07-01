import Nesterov.Chap07.Definition_7_55

-- Declarations for this item will be appended below by the statement pipeline.

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
