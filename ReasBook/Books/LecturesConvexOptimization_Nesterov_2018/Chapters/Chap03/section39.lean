import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_3_39 (from Chap03) -/
recall localizationSet

recall mem_localizationSet_iff

recall subgradientLocalizationMeasure

/- Definition 3.39 [Chapter3_3.json:138]: for a feasible region `Q`, a cut map `g`, a query
sequence `xSeq`, and a reference point `xStar`, the textbook localization set
`S_k = {x ∈ Q | ⟪g(x_i), x_i - x⟫ ≥ 0 for all i = 0, ..., k}` is the chapter owner
`localizationSet Q xSeq (g ∘ xSeq) k`, the pointwise quantities `v_i` are the localization
measures `v[g; xStar] (xSeq i)`, and the best localization radius
`v_k^* = min_{0 ≤ i ≤ k} v_i` is the owner `localization_radius xStar g xSeq k`.
The equivalent closed-ball characterization of `v_k^*` is already provided by the companion
localization-set inclusion theorems, so this item remains a pure canonical recall with no
parallel local wrapper. -/
recall localization_radius

recall localization_radius_le_measure

recall closedBall_subset_localizationSet_of_le_localization_radius

recall le_localization_radius_of_closedBall_subset_localizationSet

/-! ### Lemma_3_39 (from Chap03) -/
/-
Lemma 3.39 lies in the complete-data level-method geometric-decay domain.

Sampled owner-style declarations:
- `selected_exactValue_le_initial_gap_div_one_sub_epsilon_mul_geometric_decay` in
  `Lemma_3_3_7.lean`, the earlier chapter theorem with the same geometric-decay content and the
  sharper Lean interface keeping only the mathematically effective hypotheses;
- `HasGeometricRateOfConvergence` in `Chap01/Definition_1_2_6.lean`, the scalar owner predicate
  for geometric decay;
- `HasGeometricRateOfConvergence.of_step_bound` in `Chap01/Definition_1_2_6.lean`, the canonical
  one-step-to-geometric bridge used throughout the project;
- `constrainedMinimizationInternalGap_hasGeometricRateOfConvergence` in
  `Chap02/Proposition_2_30.lean`, the chapter style example of exposing the source-facing theorem
  through that scalar owner abstraction.

Best owner abstraction:
- source-facing owner for this exact statement:
  `selected_exactValue_le_initial_gap_div_one_sub_epsilon_mul_geometric_decay`;
- core/canonical owner beneath it: `HasGeometricRateOfConvergence`.

Primitive data:
- the scalar sequences `t` and `j`;
- the exact and estimated value families;
- the comparison, initialization, and step-size hypotheses.

Derived API:
- the geometric upper bound for the selected exact values.

Source/core/bridge triage:
- source-facing: Lemma 3.39 itself, stated in the complete-data `exactValue` / `estimatedValue`
  notation;
- core/canonical: `HasGeometricRateOfConvergence` and `of_step_bound`;
- bridge/view: the earlier chapter theorem from `Lemma_3_3_7`, whose parameter name `ε` is only a
  binder-name variation of the present source notation `α`, and whose public header already drops
  the redundant textbook-side hypotheses.

The former version of this file duplicated both the source-facing theorem and its local helper
chain. Since `Lemma_3_3_7` already owns the exact public statement, this file stays recall-only
and introduces no parallel theorem shell; the direct owner use below is a `recall` of that owner
theorem rather than a second declaration.
-/

recall selected_exactValue_le_initial_gap_div_one_sub_epsilon_mul_geometric_decay

/-! ### Proposition_3_39 (from Chap03) -/
universe u

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

namespace UniformConvexOn

/-- The pointwise maximum of two uniformly convex functions with the same modulus is uniformly
convex. -/
theorem sup
    {Q : Set E} {φ : ℝ → ℝ} {f₁ f₂ : E → ℝ}
    (hf₁ : UniformConvexOn Q φ f₁)
    (hf₂ : UniformConvexOn Q φ f₂) :
    UniformConvexOn Q φ (f₁ ⊔ f₂) := by
  refine ⟨hf₁.1, ?_⟩
  intro x hx y hy a b ha hb hab
  refine sup_le ?_ ?_
  · calc
      f₁ (a • x + b • y) ≤ a • f₁ x + b • f₁ y - a * b * φ ‖x - y‖ := hf₁.2 hx hy ha hb hab
      _ ≤ a • (f₁ x ⊔ f₂ x) + b • (f₁ y ⊔ f₂ y) - a * b * φ ‖x - y‖ := by
          gcongr <;> exact le_sup_left
  · calc
      f₂ (a • x + b • y) ≤ a • f₂ x + b • f₂ y - a * b * φ ‖x - y‖ := hf₂.2 hx hy ha hb hab
      _ ≤ a • (f₁ x ⊔ f₂ x) + b • (f₁ y ⊔ f₂ y) - a * b * φ ‖x - y‖ := by
          gcongr <;> exact le_sup_right

end UniformConvexOn

namespace StrongConvexOn

/- Proposition 3.39 lies in the strong-convexity closure domain.

Sampled owner-style declarations:
- mathlib `UniformConvexOn`
- mathlib `UniformConvexOn.mono`
- mathlib `StrongConvexOn.mono`
- mathlib `ConvexOn.sup`

Best owner abstraction:
- core/canonical closure rule: `UniformConvexOn.sup`
- source-facing specialization: `StrongConvexOn Q μ f`

Primitive data:
- the common feasible set `Q`
- the owner hypotheses `hf₁ : StrongConvexOn Q μ₁ f₁` and `hf₂ : StrongConvexOn Q μ₂ f₂`
- the common weakened modulus `min μ₁ μ₂`

Derived API:
- strong convexity of the pointwise supremum with modulus `min μ₁ μ₂`

Source/core/bridge triage:
- core/canonical: the owner-level equal-modulus closure theorem `UniformConvexOn.sup`
- source-facing: Proposition 3.39 as the quadratic-modulus specialization in the
  `StrongConvexOn` namespace
- bridge/view: weaken both moduli to `min μ₁ μ₂` via `StrongConvexOn.mono` before applying the
  canonical uniform-convexity theorem
-/

/-- Proposition 3.39: the pointwise maximum of two strongly convex functions on the same feasible
set is strongly convex with parameter `min μ₁ μ₂`. -/
-- Proof sketch: first weaken both moduli to `min μ₁ μ₂` using `StrongConvexOn.mono`, then apply
-- the owner-level equal-modulus theorem `UniformConvexOn.sup`.
theorem sup
    {Q : Set E} {f₁ f₂ : E → ℝ} {μ₁ μ₂ : ℝ}
    (hf₁ : StrongConvexOn Q μ₁ f₁)
    (hf₂ : StrongConvexOn Q μ₂ f₂) :
    StrongConvexOn Q (min μ₁ μ₂) (f₁ ⊔ f₂) := by
  have hf₁' : StrongConvexOn Q (min μ₁ μ₂) f₁ := hf₁.mono (min_le_left _ _)
  have hf₂' : StrongConvexOn Q (min μ₁ μ₂) f₂ := hf₂.mono (min_le_right _ _)
  simpa [StrongConvexOn] using UniformConvexOn.sup hf₁' hf₂'

end StrongConvexOn

/-! ### Theorem_3_39 (from Chap03) -/
open scoped LipschitzConvexProblemClass

/- Domain note: this item lies in the chapter's nonsmooth first-order black-box complexity domain.

Sampled owner-style declarations:
- `IsInLipschitzConvexProblemClass` in `Theorem_3_2_1`, the source-facing owner predicate for the
  class `𝒫(x₀, R, M)`
- `FirstOrderOracle` in `Theorem_3_2_1`, the reusable owner of valid black-box subgradient
  replies
- `SatisfiesLinearSpanCondition` in `Theorem_3_2_1`, the source-facing span predicate for iterate
  sequences
- `exists_problem_with_nonsmooth_firstOrder_lower_bound` in `Theorem_3_2_1`, the canonical
  project theorem with the same mathematical conclusion

Best owner abstraction:
- source-facing: this numbered theorem item
- core/canonical: `exists_problem_with_nonsmooth_firstOrder_lower_bound`
- bridge/view: the Chapter 1 approximate-minimizer language on `SetConstrainedMinimizationProblem`
  used downstream when the same objective-gap estimate is phrased as an approximate solution

Primitive data:
- the dimension `n`
- the starting point `x₀`
- the parameters `R`, `M : NNReal`
- the iterate index `k` with `k + 1 ≤ n`

Derived API:
- existence of a hard instance given by `f`, `xStar`, and
  `IsInLipschitzConvexProblemClass x₀ R M f xStar`
- the lower-bound conclusion for every valid subgradient oracle whose replies satisfy the
  prefix-support-growth condition, together with every iterate sequence satisfying
  `SatisfiesLinearSpanCondition`

Source/core/bridge triage:
- source-facing: Theorem 3.39 [Chapter3_2.json:71] as the textbook hard-instance lower bound
- core/canonical: `exists_problem_with_nonsmooth_firstOrder_lower_bound`
- bridge/view: the approximate-solution language in the Chapter 1 ambient owner

This theorem is semantically identical to the earlier canonical owner theorem
`exists_problem_with_nonsmooth_firstOrder_lower_bound`. The textbook bounds `R > 0`, `M > 0`, and
`0 ≤ k ≤ n - 1` are encoded in the project-facing interface as `R M : NNReal` together with
`k + 1 ≤ n`, so the clean statement for this item is a direct recall of that canonical theorem
rather than a parallel local shell.
-/

/-- Theorem 3.39 [Chapter3_2.json:71]: for `k + 1 ≤ n`, the canonical Chapter 3 hard-instance
theorem `exists_problem_with_nonsmooth_firstOrder_lower_bound` gives a convex Lipschitz objective
in `𝒫(x₀, R, M)` such that every valid first-order oracle satisfying the prefix-support-growth
condition, and every iterate sequence satisfying the linear-span condition for that oracle, has
objective gap at least `MR / (2 (2 + √(k + 1)))` at step `k`. The source inequalities `R > 0`,
`M > 0`, and `0 ≤ k ≤ n - 1` are absorbed by the project-facing parameters `R M : NNReal` and
`k + 1 ≤ n`. -/
-- The proof route is pure theorem reuse: this source-facing item is recalled with its full local
-- theorem surface, so the file stays aligned with the textbook wording without duplicating the
-- Nemirovski hard-instance construction.
recall exists_problem_with_nonsmooth_firstOrder_lower_bound
