import Mathlib
import LecturesConvexOptimization_Nesterov_2018.Chap03.Definition_3_1_1_5
import LecturesConvexOptimization_Nesterov_2018.Chap05.Definition_5_1_1
import LecturesConvexOptimization_Nesterov_2018.Chap05.FenchelPrimalExtension
import LecturesConvexOptimization_Nesterov_2018.Chap05.Lemma_5_1_6
import LecturesConvexOptimization_Nesterov_2018.Chap05.Proposition_5_0_29

-- Declarations for this item will be appended below by the statement pipeline.

open scoped ConvexAnalysis Gradient WithTopConvexAnalysis

noncomputable section

universe u

variable {E : Type u}

/- Theorem 5.1.17 lies in the chapter's Fenchel-duality / self-concordance domain.

Sampled owner-style declarations before refinement:
- `fenchelDual` / notation `f⋆` and the dual effective domain `dom (f⋆)` in
  `Chap05/Definition_5_0_27`, the chapter owner surface for Fenchel conjugacy;
- `fenchelPrimalExtension` in `Chap05/FenchelPrimalExtension`, the chapter owner for extending a
  real-valued primal function by `+∞` off a feasible set;
- `constrainedEpigraph` in `Chap03/Definition_3_3`, the chapter owner for the closed primal
  epigraph over a feasible set;
- `dom_fenchelDual_subset_image_gradient_of_selfConcordant` and
  `image_gradient_subset_dom_fenchelDual_of_selfConcordant` in `Chap05/Lemma_5_1_6`, the
  chapter's dual-domain / gradient-image bridge under the standing self-concordant hypotheses;
- `fenchelConjugate_hasGradientAt` and `fenchelConjugate_hessian_eq_inverse` in
  `Chap05/Proposition_5_0_29`, the chapter owner theorems for the gradient / inverse-Hessian
  transfer on the Fenchel dual;
- `IsSelfConcordantOnWith` in `Chap05/Definition_5_1_1`, the chapter owner for self-concordance.

Best owner abstraction:
- source-facing: the `+∞`-extension of a real-valued primal function `f` off a feasible set `Q`,
  together with the dual self-concordance transfer;
- core/canonical: `F⋆`, `dom (F⋆)`, and `extendedRealRealPart (F⋆)` for
  `F = fenchelPrimalExtension Q f`;
- bridge/view: the effective-domain identification `dom F = Q` and the chapter's Legendre /
  maximizer / inverse-Hessian bridges.

Primitive data:
- a feasible set `Q : Set E`;
- a real-valued primal function `f : E → ℝ`.

Derived API in this file:
- the self-concordance theorem on the canonical dual owner surface
  `extendedRealRealPart ((fenchelPrimalExtension Q f)⋆)`.

This file therefore reuses the extracted chapter owner `fenchelPrimalExtension` instead of
redeclaring it locally. The source-facing theorem is the dual self-concordance transfer for the
canonical Fenchel dual `extendedRealRealPart (F⋆)` under the standing primal hypotheses. A chosen
maximizer branch `xStar` and its calculus data are only bridge-level auxiliary input for the proof
route through `Proposition_5_0_29` and `5_0_30`; they do not belong on the main theorem boundary.
The closedness input is kept at the primitive owner level
`constrainedEpigraph Q (fun y ↦ (f y : WithTop ℝ))`, instead of the stronger packaged hypothesis
`ClosedConvexFunction (fenchelPrimalExtension Q f)`, because convexity is already supplied by
`IsSelfConcordantOnWith Q Mf f`. -/

variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

section

variable {Q : Set E} {Mf : NNReal} {f : E → ℝ}

local notation "F" => fenchelPrimalExtension Q f

/-- Theorem 5.1.17: let `F` be the `+∞`-extension of a real-valued function `f` off `Q`. If `f`
is self-concordant on `Q` with constant `M_f`, the constrained epigraph of `f` over `Q` is closed,
and `Q` contains no affine line, then the finite real part of the Fenchel dual `F⋆` is
self-concordant on its finite-value domain with the same constant `M_f`. This is the source-facing
owner statement: the theorem surface keeps only the standing primal hypotheses, while any chosen
maximizer branch or inverse-Hessian calculus used in a proof is auxiliary bridge data. -/
theorem fenchelPrimalExtension_dualRealPart_isSelfConcordantOnWith
    (hself : IsSelfConcordantOnWith Q Mf f)
    (hclosed :
      IsClosed (constrainedEpigraph Q (fun y ↦ (f y : WithTop ℝ))))
    (hnoAffineLine : ∀ ⦃x h : E⦄, h ≠ 0 → ¬ ∀ τ : ℝ, x + τ • h ∈ Q) :
    IsSelfConcordantOnWith
      (dom (F⋆))
      Mf
      (extendedRealRealPart (F⋆)) := by
  let _ := hself
  sorry

end

end
