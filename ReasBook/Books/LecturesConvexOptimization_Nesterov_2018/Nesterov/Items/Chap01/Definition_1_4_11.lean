import Mathlib.Tactic.Recall
import LecturesConvexOptimization_Nesterov_2018.Chap01.Definition_1_4_11

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

/-
Definition 1.4.11 is source-facing in first-order differential calculus over real normed spaces.

Relevant owner-style declarations sampled before drafting:
- `HasDerivWithinAt`
- `HasLineDerivAt`
- `HasDerivAt.hasDerivWithinAt`
- `HasFDerivAt.hasLineDerivAt`
- `hasDerivWithinAt_directionalSlice_of_differentiableAt` in
  `Nesterov/Chap01/Definition_1_4_11.lean`

Best owner abstraction:
- the one-variable right derivative
  `HasDerivWithinAt (fun α ↦ f (xBar + α • s)) Δ (Set.Ici (0 : ℝ)) 0`

Primitive data:
- `f`, `xBar`, `s`, and the derivative value `Δ`

Derived API:
- differentiability of `f` at `xBar` gives the ambient line-derivative statement
- restricting that two-sided statement to `Set.Ici 0` yields the textbook one-sided directional
  derivative along the ray

Source/core/bridge triage:
- source-facing: the right derivative of the directional slice along the ray
  `α ↦ xBar + α • s`
- core/canonical: `HasDerivWithinAt` on that scalar slice over `Set.Ici 0`
- bridge/view: the differentiability bridge through `HasLineDerivAt`

The ambient space is generalized from `ℝⁿ` to an arbitrary real normed space because no Euclidean
coordinates or finite-dimensional structure enter the owner notion or the bridge theorem. The
scalar field remains `ℝ` because the source definition is the one-sided derivative for `α ↓ 0`
along the real ray.

The source-facing owner already exists canonically in mathlib, and the chapter file already owns
the thin differentiability bridge. This item therefore exposes the owner expression directly and
recalls the companion bridge instead of keeping a duplicate local theorem body. -/

section

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {f : E → ℝ} {xBar s : E} {Δ : ℝ}

/-
Definition 1.4.11: the directional derivative of `f` at `xBar` along `s` is the right derivative
at `0` of the directional slice `α ↦ f (xBar + α • s)`. In Lean the source-facing owner is the
canonical one-variable derivative statement on `Set.Ici 0`.
-/
#check (
  HasDerivWithinAt (fun α : ℝ ↦ f (xBar + α • s)) Δ (Set.Ici (0 : ℝ)) 0
)

/-
A differentiable real-valued function has the expected one-sided derivative along every ray; this
is the chapter's thin bridge from ambient differentiability to the source-facing owner.
-/
recall hasDerivWithinAt_directionalSlice_of_differentiableAt
    {f : E → ℝ} {xBar s : E} (hf : DifferentiableAt ℝ f xBar) :
    HasDerivWithinAt (fun α : ℝ ↦ f (xBar + α • s)) (fderiv ℝ f xBar s) (Set.Ici (0 : ℝ)) 0

end
