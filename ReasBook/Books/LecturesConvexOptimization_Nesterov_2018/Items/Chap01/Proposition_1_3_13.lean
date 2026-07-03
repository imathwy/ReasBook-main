import Mathlib.Tactic.Recall
import LecturesConvexOptimization_Nesterov_2018.Chap01.Proposition_1_3_13

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory intervalIntegral

/- Proposition 1.3.13 lies in the one-dimensional interval-integral / Lipschitz-Riemann-sum
domain.

Relevant owner-style declarations sampled before refining:
* `uniformGridRiemannSum` in `LecturesConvexOptimization_Nesterov_2018/Chap01/Definition_1_3_12.lean`, the chapter owner for the
  source-facing right-endpoint sampled sum
* `abs_intervalIntegral_sub_uniformGridRiemannSum_le` in
  `LecturesConvexOptimization_Nesterov_2018/Chap01/Proposition_1_3_13.lean`, the chapter owner of the sharp `L / (2N)` estimate
* `abs_intervalIntegral_sub_uniformGridRiemannSum_le_eps` in
  `LecturesConvexOptimization_Nesterov_2018/Chap01/Proposition_1_3_13.lean`, the chapter owner of the epsilon corollary
* `LipschitzOnWith`, the canonical mathlib owner for the Lipschitz hypothesis on `[0, 1]`

Best owner abstraction:
* source-facing: the approximation error between `∫ x in (0 : ℝ)..1, f x` and the right-endpoint
  uniform-grid Riemann sum on `[0, 1]`
* core/canonical: `uniformGridRiemannSum f N` together with
  `abs_intervalIntegral_sub_uniformGridRiemannSum_le`
* bridge/view: the explicit finite-sum formula for `uniformGridRiemannSum`, already recalled in
  `Items/Chap01/Definition_1_3_12.lean`

Primitive data:
* `f : ℝ → ℝ`
* `L : NNReal`
* `N : ℕ+`
* the owner hypothesis `LipschitzOnWith L f (Set.Icc (0 : ℝ) 1)`

Derived API:
* the sharp bound `|(∫_0^1 f) - uniformGridRiemannSum f N| ≤ L / (2N)`
* the epsilon corollary under `(L : ℝ) / (2 * ε) ≤ N`

Source/core/bridge triage:
* source-facing: the textbook right-endpoint uniform-grid approximation statement
* core/canonical: the chapter theorem stated with the owner `uniformGridRiemannSum`
* bridge/view: the explicit textbook finite-sum expansion of that owner

This item is recall-first: the chapter file already owns the source-faithful theorem and its
epsilon corollary, so the item file reuses those declarations directly instead of keeping a
parallel theorem pair with the sampled sum expanded inline. -/

/- Proposition 1.3.13: if `f` is `L`-Lipschitz on `[0, 1]`, then the right-endpoint
uniform-grid Riemann sum approximates `∫ x in (0 : ℝ)..1, f x` with error at most `L / (2N)`. -/
recall abs_intervalIntegral_sub_uniformGridRiemannSum_le
    (f : ℝ → ℝ) (L : NNReal) (N : ℕ+)
    (hLip : LipschitzOnWith L f (Set.Icc (0 : ℝ) 1)) :
    |(∫ x in (0 : ℝ)..1, f x) - uniformGridRiemannSum f N| ≤ (L : ℝ) / (2 * (N : ℝ))

/- If `N` is at least `L / (2ε)`, then the uniform-grid Riemann sum error is at most `ε`. -/
recall abs_intervalIntegral_sub_uniformGridRiemannSum_le_eps
    (f : ℝ → ℝ) (L : NNReal) (N : ℕ+) {ε : ℝ}
    (hLip : LipschitzOnWith L f (Set.Icc (0 : ℝ) 1))
    (hε : 0 < ε)
    (hNε : (L : ℝ) / (2 * ε) ≤ (N : ℝ)) :
    |(∫ x in (0 : ℝ)..1, f x) - uniformGridRiemannSum f N| ≤ ε
