import Mathlib.Tactic.Recall
import Nesterov.Chap04.Lemma_4_1_4

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Gradient CubicRegularizationModelNotation

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

section

variable {L3 : NNReal} {f : E → ℝ} {M : ℝ} {x T : E}

/- Text 4.2.8 lies in the cubic-regularization / second-order smooth optimization domain on real
Hilbert spaces.

Sampled owner-style declarations:
* `cubicRegularizationQuadraticApproximation` in `Definition_4_1_3`, the chapter owner for the
  cubic model;
* `gradient_norm_le_of_isMinOn_cubicRegularizationQuadraticApproximation` in `Lemma_4_1_4`, the
  owner-level gradient estimate for cubic-model minimizers;
* `objective_sub_cubicRegularizationValue_ge_residual_cube` in `Lemma_4_1_5`, the owner-level
  lower bound on `f x - \bar f_M(x)`;
* `objective_cubicTrialPoint_le_cubicRegularizationValue_of_le_hessianLipschitz` in
  `Lemma_4_1_5`, the bridge comparing a minimizing trial point with `\bar f_M(x)`.

Best owner abstraction:
* the chapter cubic-model owner `m[f; M](x)`
* the owner theorem
  `gradient_norm_le_of_isMinOn_cubicRegularizationQuadraticApproximation`
* the owner value `cubicRegularizationValue f M x`

Primitive data:
* for the recall item, no new primitive data beyond the imported owner theorem;
* for the new source-facing estimate, the cubic model
  `m[f; M](x)`, a global minimizer witness
  `hT : IsMinOn (m[f; M](x)) Set.univ T`, and the owner
  hypotheses `hf : f ∈ C22[L3]`, `hf_conv : ConvexOn ℝ Set.univ f`, and `hML : (L3 : ℝ) ≤ M`

Derived API:
* the direct recall of Text 4.2.8 (1) from `Lemma_4_1_4`
* the objective decrease estimate under convexity and `M ≥ L3`

Source/core/bridge triage:
* source-facing: Text 4.2.8 (2)
* core/canonical: `m[f; M](x)`, `cubicRegularizationValue`, and the owner theorem from
  `Lemma_4_1_4`
* bridge/view: specializing those owners to a global minimizer `T`

The previous version duplicated the Chapter 4 owner theorem
`gradient_norm_le_of_isMinOn_cubicRegularizationQuadraticApproximation` and even strengthened its
assumptions from `0 ≤ M` to `0 < M`. This refinement removes that duplicate wheel: part (1) is a
pure recall, while part (2) remains the only fresh source-facing declaration in this file. -/

/- Text 4.2.8 (1) is the direct Chapter 4 recall of the owner theorem from `Lemma_4_1_4`; this
file keeps no parallel local theorem shell. -/
recall gradient_norm_le_of_isMinOn_cubicRegularizationQuadraticApproximation

-- Proof sketch: compare `f T` with `m[f; M](x; T)` using the
-- Chapter 4 objective-versus-model upper bound from `Lemma_4_1_5`, use the minimizing property
-- against the competitor `x`, and then rewrite the resulting cubic-model gap using the
-- first-order optimality relation of the minimizer. Convexity keeps the Hessian quadratic term
-- nonnegative, leaving the factor `(M / 3) ‖x - T‖³`.
/-- If `f` is convex, `f ∈ C22[L3]`, and `M ≥ L₃`, then every cubic-step minimizer `T`
satisfies `f x - f T ≥ (M / 3) ‖x - T‖³`. -/
theorem convex_sub_ge_of_isMinOn_cubicRegularizationQuadraticApproximation
    (hf : f ∈ C22[L3]) (hf_conv : ConvexOn ℝ Set.univ f) (hML : (L3 : ℝ) ≤ M)
    (hT : IsMinOn (m[f; M](x)) Set.univ T) :
    f x - f T ≥ (M / 3 : ℝ) * ‖x - T‖ ^ (3 : ℕ) := sorry

end
