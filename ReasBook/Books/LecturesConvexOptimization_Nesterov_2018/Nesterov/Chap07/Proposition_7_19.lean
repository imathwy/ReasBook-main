import LecturesConvexOptimization_Nesterov_2018.Nesterov.Chap03.Definition_3_9
import LecturesConvexOptimization_Nesterov_2018.Nesterov.Chap07.Definition_7_42

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped SupportFunction

universe u v

variable {ι : Type u} [Fintype ι] [Nonempty ι]
variable {E : Type v} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/- Proposition 7.19 lies in Chapter 7's finite-range support-function / log-sum-exp smoothing
domain.

Sampled owner-style declarations:
- `ξ[Q]` and `supportFunction_apply` in `Chap03/Definition_3_9`, the chapter owner for support
  functions;
- `supportFunction_range_toReal_eq_sSup_inner` in `Chap07/Lemma_7_1`, the nearby finite-range
  evaluation theorem for `ξ[Set.range a]`;
- `smoothMaxInnerApproximation` and `smoothMaxInnerApproximation_apply` in
  `Chap07/Definition_7_42`, the chapter owner for the positive-parameter log-sum-exp smoothing of
  `x ↦ max_i ⟪aᵢ, x⟫`;
- `HasDiagonalOrthantSupportBounds` in `Chap07/Proposition_7_21`, the direct downstream support-
  function surface for the same finite family `a`.

Best owner abstraction:
- source-facing: Proposition 7.19's smoothing bound for the support function of `Set.range a`;
- core/canonical: `ξ[Set.range a]` and `smoothMaxInnerApproximation a μ`;
- bridge/view: the finite-max evaluation
  `maxTypeObjective (fun i y ↦ inner ℝ (a i) y) x = (ξ[Set.range a] x).toReal`.

Primitive data:
- the finite nonempty index type `ι`;
- the vectors `a : ι → E`;
- the positive smoothing parameter `μ : {μ : ℝ // 0 < μ}`.

Derived API:
- the canonical support-function owner `(ξ[Set.range a] x).toReal`;
- the canonical smoothing owner `smoothMaxInnerApproximation a μ`;
- the additive error term `(μ : ℝ) * Real.log (Fintype.card ι)`.

This refinement keeps Proposition 7.19 on the intrinsic Chapter 3 support-function owner instead
of the lower-level finite-max owner. The finite maximum remains only a bridge/view to this support
function surface, matching the surrounding Chapter 7 API in `Lemma_7_1` and `Proposition_7_21`.
-/

/-- Proposition 7.19: for a finite nonempty family `aᵢ` in a real inner product space, the
log-sum-exp smoothing of the support function of `Set.range a` lies between
`(ξ[Set.range a] x).toReal` and the same quantity plus `μ log (Fintype.card ι)` at every point
`x`, for every positive smoothing parameter `μ`. -/
-- Proof sketch: let `M = (ξ[Set.range a] x).toReal`, equivalently
-- `M = max_i ⟪aᵢ, x⟫`. Every summand `exp (⟪aᵢ, x⟫ / μ)` is at most `exp (M / μ)`, so the whole
-- sum is at most `Fintype.card ι * exp (M / μ)`, which gives the upper bound after applying
-- `μ * log`. Since the finite maximum is attained, one summand is exactly `exp (M / μ)`, so the
-- sum is at least that term, yielding the lower bound.
theorem supportFunction_range_toReal_smoothing_bounds
    (a : ι → E) (μ : {μ : ℝ // 0 < μ}) (x : E) :
    (ξ[Set.range a] x).toReal ≤ smoothMaxInnerApproximation a μ x ∧
      smoothMaxInnerApproximation a μ x ≤
        (ξ[Set.range a] x).toReal +
          (μ : ℝ) * Real.log (Fintype.card ι) := sorry

end
