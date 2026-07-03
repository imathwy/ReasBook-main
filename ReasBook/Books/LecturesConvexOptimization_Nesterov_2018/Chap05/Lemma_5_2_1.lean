import Mathlib
import LecturesConvexOptimization_Nesterov_2018.Chap05.Definition_5_1_1
import LecturesConvexOptimization_Nesterov_2018.Chap05.Definition_5_2_1

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Gradient NewtonDecrement
open SelfConcordantNewtonVariant

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/- Lemma 5.2.1 lies in the Chapter 5 self-concordant intermediate-Newton domain.

Sampled owner declarations:
* `selfConcordantNewtonNextPoint` in `Definition_5_2_1`, the Chapter 5 owner for one-step
  self-concordant Newton updates;
* `NewtonDecrement.ofDetNeZero` in `Definition_5_0_24`, the Chapter 5 owner for the Newton
  decrement at a domain point with nondegenerate Hessian;
* `DampedNewton.Method.IsSelfConcordant` in `Definition_5_2_1`, the Chapter 5 refinement of the
  recursive damped Newton iterate sequence;
* `selfConcordant_dampedNewtonStep_value_decrease` in `Theorem_5_1_15`, the nearby one-step
  value-decrease owner for the damped variant.

Best owner abstraction:
* source-facing: the value drop along the intermediate Newton iterates;
* core/canonical: the one-step update `selfConcordantNewtonNextPoint` together with
  `NewtonDecrement.ofDetNeZero`;
* bridge/view: the recursive method step `x_{k+1}` obtained from the method package.

Primitive data:
* a self-concordant function `f` on `dom` with parameter `Mf`;
* a point `x ∈ dom`;
* Hessian nondegeneracy at `x`.

Derived API:
* the one-step intermediate update
  `selfConcordantNewtonNextPoint f Mf .intermediate x hx hH`;
* the Newton decrement `NewtonDecrement.ofDetNeZero Mf f hx hH`;
* the method-level successor `method (k + 1)`, recovered from the canonical one-step owner.

This refinement keeps the iterate-level textbook lemma, but no longer treats the recursive method
package as primitive data for the inequality itself. The file now centers the one-step owner
surface and derives the method statement from it. -/

section

variable {dom : Set E} {Mf : NNReal} {f : E → ℝ}
variable [IsSelfConcordantOnWith dom Mf f]

-- Proof sketch: apply the self-concordant upper Taylor bound to the intermediate Newton update
-- `x_{k+1} = x_k - (1 + ξ_k)⁻¹ [∇²f(x_k)]⁻¹ ∇f(x_k)` with
-- `ξ_k = M_f² λ_k² / (1 + M_f λ_k)`, then rewrite the resulting `ω_*` term using the rational
-- lower bound from Lemma 5.1.5 and simplify the scalar expression exactly as in the textbook.
-- No positivity hypothesis on `M_f` is needed: at `M_f = 0`, the intermediate shift is `0` and
-- the displayed lower bound collapses to `δ² / 2`.
/-- The intermediate self-concordant Newton step decreases the objective by at least the explicit
rational function of the Newton decrement. -/
theorem selfConcordant_intermediateNewtonStep_value_drop_lower_bound
    (Mf : NNReal) [IsSelfConcordantOnWith dom Mf f] {x : E}
    (hx : x ∈ dom) (hH : (hessian f x).det ≠ 0) :
    let δ := NewtonDecrement.ofDetNeZero Mf f hx hH
    let xPlus := selfConcordantNewtonNextPoint f Mf .intermediate x hx hH
    f x - f xPlus ≥
      δ ^ 2 / (2 * (1 + (Mf : ℝ) * δ + (Mf : ℝ) ^ 2 * δ ^ 2)) +
        (Mf : ℝ) * δ ^ 3 / (2 * (1 + (Mf : ℝ) * δ) * (3 + 2 * (Mf : ℝ) * δ)) := sorry

-- Proof sketch: specialize `selfConcordant_intermediateNewtonStep_value_drop_lower_bound` to the
-- iterate `x_k`, then rewrite the successor `x_{k+1}` through the canonical one-step owner
-- `selfConcordantNewtonNextPoint`. As above, no separate positivity hypothesis on `M_f` is part
-- of the mathematical data.
/-- Lemma 5.2.1: along the intermediate self-concordant Newton method `(5.2.1)C`, the objective
drop from `x_k` to `x_{k+1}` is bounded below by the explicit rational function of the Newton
decrement `λ_k`. This is the textbook inequality `(5.2.2)`. -/
lemma intermediateNewton_value_drop_lower_bound
    {x0 : E}
    (method : DampedNewton.Method f x0)
    (hmethod : method.IsSelfConcordant dom Mf .intermediate)
    (k : ℕ) :
    let δ :=
      NewtonDecrement.ofDetNeZero Mf f (hmethod.iterates_mem k) (method.hessian_nondegenerate k)
    f (method k) - f (method (k + 1)) ≥
      δ ^ 2 / (2 * (1 + (Mf : ℝ) * δ + (Mf : ℝ) ^ 2 * δ ^ 2)) +
        (Mf : ℝ) * δ ^ 3 / (2 * (1 + (Mf : ℝ) * δ) * (3 + 2 * (Mf : ℝ) * δ)) := by
  simpa [hmethod.succ_eq_nextPoint k] using
    (selfConcordant_intermediateNewtonStep_value_drop_lower_bound
      Mf (hmethod.iterates_mem k) (method.hessian_nondegenerate k))

end
