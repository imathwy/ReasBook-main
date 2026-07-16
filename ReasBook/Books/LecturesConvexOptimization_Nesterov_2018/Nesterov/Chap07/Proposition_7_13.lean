import LecturesConvexOptimization_Nesterov_2018.Nesterov.Chap07.Proposition_7_12
import LecturesConvexOptimization_Nesterov_2018.Nesterov.Chap07.Proposition_7_14

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
