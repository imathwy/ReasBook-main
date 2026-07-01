import Nesterov.Chap02.Definition_2_17

open scoped Gradient

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/- Primary domain: smooth strongly convex objectives on real Hilbert spaces.

Relevant owner-style declarations sampled before refining this file:
* `IsStrongConvexSmoothObjective` in `Definition_2_17`
* `IsStrongConvexSmoothObjective.gradient_strong_mono` in `Definition_2_17`
* `IsStrongConvexSmoothObjective.lower_tangent_quadratic` in `Definition_2_17`
* `IsStrongConvexSmoothObjective.upper_tangent_quadratic` in `Definition_2_17`

Owner-layer triage:
* source-facing: Theorem 2.13 on `ℝⁿ`
* core/canonical: `IsStrongConvexSmoothObjective μ L f`
* bridge/view: the Euclidean specialization used later in Chapter 2

Primitive data in the owner abstraction:
* positivity of `μ`
* global `C¹` regularity
* `μ`-strong convexity on the whole space
* the `L`-gradient-Lipschitz bound

Derived API:
* strong gradient monotonicity
* the secant inequality below

The strengthened secant inequality is therefore kept as owner-derived API in the namespace
`IsStrongConvexSmoothObjective`, rather than through a second Euclidean wrapper. -/

namespace IsStrongConvexSmoothObjective

variable {μ L : ℝ} {f : E → ℝ}

/- Theorem 2.13 is stated in the text on `ℝⁿ`; the owner theorem below records the same statement
for the ambient real Hilbert-space abstraction, and hence specializes back to the Euclidean case.
The parameter relation `μ ≤ L` is not kept as primitive public data: on nontrivial spaces it is a
derived consequence of `hf`, while on subsingleton spaces the displayed inequality is trivial. -/
/-- Theorem 2.13: a function in `𝓢^{1,1}_{μ,L}` satisfies the strengthened secant inequality
`⟪∇ f x - ∇ f y, x - y⟫ ≥ (μ L / (μ + L)) ‖x - y‖² + (1 / (μ + L)) ‖∇ f x - ∇ f y‖²`
for all `x, y`. -/
-- Proof sketch: use the owner theorem `hf.gradient_strong_mono` together with the gradient
-- Lipschitz bound, apply
-- the same owner-side secant argument to the shifted objective `z ↦ f z - (μ / 2) * ‖z‖²`, and
-- rearrange the resulting
-- inequality. The endpoint case `μ = L` gives equality.
theorem pairing_lower_bound
    (hf : IsStrongConvexSmoothObjective μ L f)
    (x y : E) :
    inner ℝ (∇ f x - ∇ f y) (x - y) ≥
      (μ * L / (μ + L)) * ‖x - y‖ ^ 2 +
        (1 / (μ + L)) * ‖∇ f x - ∇ f y‖ ^ 2 := sorry

end IsStrongConvexSmoothObjective
