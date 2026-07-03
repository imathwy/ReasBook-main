import Mathlib
import Nesterov.Chap03.Definition_3_1_1_5

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

variable {X : Type u} [TopologicalSpace X] [AddCommMonoid X] [Module ℝ X]

/- Theorem 3.1.5 is the owner closure-calculus file for closed convex `WithTop ℝ`-valued
functions on feasible sets.

Primary domain:
- closed-convex extended-real-valued functions on real topological modules.

Sampled owner-style declarations in this domain:
- `ClosedConvexOn` from `Definition_3_1_1_5`
- mathlib `ConvexOn.smul`
- mathlib `ConvexOn.add`
- mathlib `ConvexOn.sup`

Best owner abstraction:
- source-facing owner: `ClosedConvexOn Q f`
- core/canonical supporting layer: `ConvexOn ℝ Q (withTopRealPart f)` together with the pointwise
  function operations `•`, `+`, and `⊔`

Primitive data:
- the owner witnesses `hf`, `hf₁`, `hf₂`
- the scalar `β` together with the nonnegativity hypothesis `0 ≤ β`

Derived API:
- the three closure theorems below

Source/core/bridge triage:
- source-facing: the scalar-multiple, sum, and pointwise-maximum closure rules recorded under
  Theorem 3.1.5
- core/canonical: `ClosedConvexOn` and the corresponding `ConvexOn` function operations
- bridge/view: `ClosedConvexOn.convexOn_withTopRealPart`, which transports the owner statement to
  the canonical convex-function surface

The public API therefore stays at the `ClosedConvexOn` owner level, but it uses the canonical
pointwise function owners where available instead of longer theorem-local lambda spellings.
-/

namespace ClosedConvexOn

/-- Theorem 3.1.5 (1): multiplying a closed convex function by a nonnegative scalar preserves
closedness and convexity on the same feasible set; the canonical pointwise owner is
`(β : WithTop ℝ) • f`. -/
-- Proof sketch: identify the constrained epigraph of `x ↦ β • f₁ x` with the epigraph of `f₁`
-- under the height rescaling by `β`; convexity is preserved by nonnegative scalar multiplication,
-- and closedness follows from continuity of the rescaling map.
theorem nonneg_smul
    {Q : Set X} {f : X → WithTop ℝ} {β : ℝ}
    (hf : ClosedConvexOn Q f) (hβ : 0 ≤ β) :
    ClosedConvexOn Q ((β : WithTop ℝ) • f) := sorry

/-- Theorem 3.1.5 (2): the sum of two closed convex functions is closed and convex on the
intersection of their feasible sets. -/
-- Proof sketch: restrict both functions to `Q₁ ∩ Q₂`; convexity is preserved by pointwise
-- addition, and closedness follows from the standard epigraph or lower-semicontinuity argument for
-- sums on a common feasible domain.
theorem add_inter
    {Q₁ Q₂ : Set X} {f₁ f₂ : X → WithTop ℝ}
    (hf₁ : ClosedConvexOn Q₁ f₁) (hf₂ : ClosedConvexOn Q₂ f₂) :
    ClosedConvexOn (Q₁ ∩ Q₂) (f₁ + f₂) := sorry

/-- Theorem 3.1.5 (3): the pointwise maximum of two closed convex functions is closed and convex
on the intersection of their feasible sets; the canonical pointwise owner is `f₁ ⊔ f₂`. -/
-- Proof sketch: the constrained epigraph of `f₁ ⊔ f₂` over `Q₁ ∩ Q₂` is the intersection of the
-- constrained epigraphs of `f₁` and `f₂`, and intersections preserve both closedness and
-- convexity.
theorem max_inter
    {Q₁ Q₂ : Set X} {f₁ f₂ : X → WithTop ℝ}
    (hf₁ : ClosedConvexOn Q₁ f₁) (hf₂ : ClosedConvexOn Q₂ f₂) :
    ClosedConvexOn (Q₁ ∩ Q₂) (f₁ ⊔ f₂) := sorry

end ClosedConvexOn

end
