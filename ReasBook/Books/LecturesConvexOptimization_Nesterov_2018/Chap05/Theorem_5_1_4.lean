import Mathlib
import LecturesConvexOptimization_Nesterov_2018.Chap05.Definition_5_1_1

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Gradient HessianLocalNorm

noncomputable section

universe u

/- Theorem 5.1.4 lies in the Chapter 5 self-concordance / logarithmic-barrier domain.

Sampled owner-style declarations in this domain:
* `IsSelfConcordantOnWith` from `Definition_5_1_1`, the constant-bearing chapter owner for
  self-concordance on a domain;
* `IsSelfConcordantOnWith.hessian_isPositive` from `Definition_5_1_1`, the chapter bridge from
  self-concordance to the pointwise Hessian-positivity owner;
* `hessianLocalNorm` from `Definition_5_1_1`, the chapter owner for the Hessian-induced local
  norm used by later barrier-parameter APIs;
* `IsSelfConcordantBarrierOnWith` from `Definition_5_3_2`, the barrier analogue used downstream;
* `hessian` from `Chap01/Definition_1_4_16`, the canonical second-order owner;
* `convexOn_iff_hessian_isPositive` from `Chap02/Theorem_2_4`, the local owner-level Hessian
  positivity criterion for convex `C²` data.

Source/core/bridge triage:
* source-facing: the logarithmic barrier `x ↦ -log (β - f x)`;
* core/canonical: `ContinuousLinearMap.IsPositive (hessian f x)` for the Hessian comparison
  clause, and `IsSelfConcordantOnWith dom Mf f` for the quantitative self-concordance clause;
* bridge/view: the textbook positivity estimate `0 < β - f x` on that strict sublevel set.

Primitive data:
* the function `f`;
* the threshold `β`;
* the ambient domain `dom`;
* the self-concordance owner `IsSelfConcordantOnWith dom Mf f`, which supplies the `C³`
  regularity and pointwise Hessian positivity needed for clauses (2) and (3).

Derived API:
* the strict sublevel set itself, expressed directly by the canonical set-builder rather than a
  second packaged owner;
* the barrier-gradient square estimate on the owner surface `‖h‖[sublevelLogBarrier f β; x]`,
  stated directly on `IsSelfConcordantOnWith dom Mf f` so that the required differential
  regularity remains explicit in the public API;
* the self-concordance constant formula, used directly in the main theorem rather than through a
  one-off wrapper.

This file therefore keeps the barrier as the source-facing owner and deletes the duplicate-wheel
derived wrappers around its natural domain and parameter formula. -/

variable {E : Type u}

/-- The logarithmic barrier associated with the strict sublevel set `{x | f x < β}` is
`x ↦ -log (β - f x)`. -/
def sublevelLogBarrier (f : E → ℝ) (β : ℝ) : E → ℝ :=
  fun x ↦ -Real.log (β - f x)

/-- Evaluating `sublevelLogBarrier f β` recovers the textbook formula `-log (β - f x)`. -/
@[simp]
theorem sublevelLogBarrier_apply (f : E → ℝ) (β : ℝ) (x : E) :
    sublevelLogBarrier f β x = -Real.log (β - f x) :=
  rfl

/-- Theorem 5.1.4 (1): on the strict sublevel set `{x | f x < β}`, the logarithmic barrier
`x ↦ -log (β - f x)` is well defined because its argument is positive. -/
-- Proof sketch: if `f x < β`, then `0 < β - f x`; this is exactly the positivity needed for
-- `Real.log (β - f x)`.
theorem sublevelLogBarrier_arg_pos_of_mem_domain
    (f : E → ℝ) (β : ℝ) {x : E} (hx : f x < β) :
    0 < β - f x := sorry

variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

section SublevelLogBarrier

variable {dom : Set E} {Mf : NNReal} {f : E → ℝ}

namespace IsSelfConcordantOnWith

/-- Theorem 5.1.4 (2): at every point of the strict sublevel set `{x | f x < β}` inside the
domain of a self-concordant function, the Hessian quadratic form of `x ↦ -log (β - f x)`
dominates the square of the gradient pairing. -/
-- Proof sketch: `hself.contDiffOn` supplies the second-order regularity needed to differentiate
-- `τ ↦ -log (β - f (x + τ • h))` twice, while `hself.hessian_isPositive hx` makes the Hessian
-- contribution nonnegative.
theorem sublevelLogBarrier_hessian_quadraticForm_ge_gradient_sq
    (hself : IsSelfConcordantOnWith dom Mf f) (β : ℝ) {x h : E}
    (hx : x ∈ dom) (hβ : f x < β) :
    inner ℝ h (hessian (sublevelLogBarrier f β) x h) ≥
      (inner ℝ (∇ (sublevelLogBarrier f β) x) h) ^ (2 : ℕ) := sorry

/-- Theorem 5.1.4 (2), owner-level bridge: for a self-concordant input, the square of the
gradient pairing of `x ↦ -log (β - f x)` is bounded by the square of the canonical Hessian local
norm. -/
theorem sublevelLogBarrier_gradient_inner_sq_le
    (hself : IsSelfConcordantOnWith dom Mf f) (β : ℝ) {x h : E}
    (hx : x ∈ dom) (hβ : f x < β) :
    (inner ℝ (∇ (sublevelLogBarrier f β) x) h) ^ (2 : ℕ) ≤
      ‖h‖[sublevelLogBarrier f β; x] ^ (2 : ℕ) := sorry

end IsSelfConcordantOnWith

/-- Theorem 5.1.4 (3): if `f` is bounded below on `dom` by `f*`, then the barrier
`x ↦ -log (β - f x)` is self-concordant on `{x ∈ dom | f x < β}` with constant
`sqrt (1 + M_f^2 * (β - f*))`. -/
-- Proof sketch: compute the third directional derivative of `x ↦ -log (β - f x)` and rewrite it
-- in terms of the Hessian quadratic form and gradient pairing of `f`. Use the self-concordance
-- inequality for `f`, the quadratic-form lower bound from the previous clause applied to the
-- pointwise Hessian-positivity owner furnished by `hself.hessian_isPositive hx`, and the estimate
-- `β - f x ≤ β - f*` coming from the lower bound hypothesis to obtain the stated constant; when
-- `β ≤ f*`, the strict sublevel domain is empty, so the same statement remains valid without a
-- separate positivity hypothesis on `β - f*`.
theorem sublevelLogBarrier_isSelfConcordantOnWith
    (hself : IsSelfConcordantOnWith dom Mf f) (β fStar : ℝ)
    (h_lower : ∀ ⦃x : E⦄, x ∈ dom → fStar ≤ f x) :
    IsSelfConcordantOnWith
      {x : E | x ∈ dom ∧ f x < β}
      (NNReal.sqrt (1 + Mf ^ (2 : ℕ) * Real.toNNReal (β - fStar)))
      (sublevelLogBarrier f β) := sorry

end SublevelLogBarrier

end
