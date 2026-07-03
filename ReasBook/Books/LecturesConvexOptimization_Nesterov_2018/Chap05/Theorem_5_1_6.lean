import Mathlib
import Nesterov.Chap03.Definition_3_3
import Nesterov.Chap05.Definition_5_0_23
import Nesterov.Chap05.Definition_5_1_1

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

/-
Theorem 5.1.6 belongs to the Chapter 5 self-concordance / closed-convex domain.

Sampled owner-style declarations in this domain:
* `IsSelfConcordantOn` from `Definition_5_1_1`, the source-facing qualitative owner when the
  value of the self-concordance constant is not part of the statement;
* `HasPositiveDefiniteHessianOn` from `Definition_5_0_23`, the chapter owner for pointwise
  Hessian positivity together with strict Hessian quadratic-form positivity on a domain;
* `IsSelfConcordantOnWith` from `Definition_5_1_1`, the quantitative owner used only after
  unpacking a witness from `IsSelfConcordantOn`;
* `hessian` from `Chap01/Definition_1_4_16`, the canonical second-order owner replacing the raw
  `fderiv ℝ (∇ f)` shell;
* `hessianLocalNorm` and `hessianLocalNorm_def` from `Definition_5_1_1`, the canonical bridge
  from the Hessian owner to the local norm;
* `constrainedEpigraph` from `Chap03/Definition_3_3`, the chapter owner for the source epigraph
  over a feasible domain, whose closedness supplies the missing hypothesis from the source
  theorem.

Source/core/bridge triage:
* source-facing: strict positivity of the Hessian quadratic form in every nonzero direction under
  qualitative self-concordance and the source no-affine-line hypothesis;
* core/canonical: `HasPositiveDefiniteHessianOn dom f`, the Hessian owner `hessian f x`, and the
  Chapter 3 constrained-epigraph owner on `dom`;
* bridge/view: pointwise positivity and strict local-norm positivity read canonically via
  `HasPositiveDefiniteHessianOn.hessian_isPositive_of_mem`,
  `HasPositiveDefiniteHessianOn.posdef`, and `hessianLocalNorm_def`.

Primitive data:
* the ambient complete real inner-product space `E`;
* a domain `dom`, objective `f`, and the closed constrained epigraph
  `constrainedEpigraph dom (fun y ↦ (f y : WithTop ℝ))`;
* the no-affine-line hypothesis on `dom`.

Derived API:
* the chapter owner `HasPositiveDefiniteHessianOn dom f`.

This file keeps the numbered theorem source-facing, but its core output is now the chapter owner
`HasPositiveDefiniteHessianOn dom f`. Downstream pointwise Hessian and local-norm positivity are
read from that owner through `HasPositiveDefiniteHessianOn.hessian_isPositive_of_mem`,
`HasPositiveDefiniteHessianOn.posdef`, and `hessianLocalNorm_def` instead of new local wrapper
theorems. -/

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

namespace IsSelfConcordantOn

variable {dom : Set E} {f : E → ℝ}

-- Proof sketch: if the Hessian quadratic form vanished at some `x ∈ dom` in a nonzero direction
-- `h`, then the restriction of `f` to the affine line `x + ℝ • h` would be locally affine at
-- `x`. Closedness of the constrained epigraph upgrades this local zero-curvature behavior to an
-- entire affine line in `dom`, contradicting the source hypothesis.
/-- Theorem 5.1.6: if `f` is self-concordant on `dom`, the constrained epigraph of `f` over
`dom` is closed, and `dom` contains no affine line, then the Hessian of `f` is positive definite
on `dom`. -/
theorem hasPositiveDefiniteHessianOn_of_no_affine_line
    (hself : IsSelfConcordantOn dom f)
    (hclosed : IsClosed (constrainedEpigraph dom (fun y ↦ (f y : WithTop ℝ))))
    (hnoAffineLine : ∀ ⦃x h : E⦄, h ≠ 0 → ¬ ∀ τ : ℝ, x + τ • h ∈ dom) :
    HasPositiveDefiniteHessianOn dom f := by
  rcases hself with ⟨Mf, hMf⟩
  letI := hMf
  refine ⟨?_, ?_⟩
  · intro x hx
    exact IsSelfConcordantOnWith.hessian_isPositive_of_mem Mf hx
  · intro x hx h hh
    sorry

end IsSelfConcordantOn

end
