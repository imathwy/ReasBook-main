import Mathlib.Tactic.Recall
import LecturesConvexOptimization_Nesterov_2018.Nesterov.Chap01.Lemma_1_4_10

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped Gradient

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-
Lemma 1.4.10 lies in the tangent-direction geometry of differentiable level sets.

Relevant owner-style declarations sampled before refinement:
* `posTangentConeAt`, the mathlib tangent-cone owner underlying this domain;
* `tangentDirectionsToLevelSet`, the chapter source-facing owner for unit tangent directions to a
  level set;
* `mem_tangentDirectionsToLevelSet_iff_exists_level_set_secant_limit`, the normalized-secant
  bridge from the textbook formulation to that owner;
* `inner_gradient_eq_zero_of_mem_tangentDirectionsToLevelSet`, the upstream owner theorem proving
  orthogonality of tangent directions to the gradient.

Source/core/bridge triage:
* source-facing: tangent directions to the level set through `xbar`;
* core/canonical: `posTangentConeAt (f ⁻¹' {f xbar}) xbar`, surfaced in this chapter through
  `tangentDirectionsToLevelSet f xbar`;
* bridge/view: `mem_tangentDirectionsToLevelSet_iff_exists_level_set_secant_limit`, which keeps
  the textbook secant-limit formulation as a companion characterization.

Primitive data:
* `f : E → ℝ`, `xbar : E`, `s : E`;
* differentiability of `f` at `xbar`;
* owner-level membership `s ∈ tangentDirectionsToLevelSet f xbar`.

Derived API:
* the secant-limit existence criterion from Definition 1.4.9;
* orthogonality to the gradient from the upstream owner theorem.

The previous version duplicated that bridge on the theorem surface by taking existential secant
data as primitive input. This refinement removes the duplicate wheel and keeps the numbered item
as direct recall of the chapter owner theorem; the secant-limit formulation remains available via
Definition 1.4.9.
-/

/- Lemma 1.4.10: if `f` is differentiable at `xbar`, then every tangent direction to the level
set of `f` at `xbar` is orthogonal to the gradient at `xbar`. -/
recall inner_gradient_eq_zero_of_mem_tangentDirectionsToLevelSet
    {f : E → ℝ} {xbar s : E} (hf : DifferentiableAt ℝ f xbar)
    (hs : s ∈ tangentDirectionsToLevelSet f xbar) :
    inner ℝ (∇ f xbar) s = 0
