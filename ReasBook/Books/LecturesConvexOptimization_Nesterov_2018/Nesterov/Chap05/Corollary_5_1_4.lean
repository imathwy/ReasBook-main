import Mathlib
import LecturesConvexOptimization_Nesterov_2018.Nesterov.Chap05.Definition_5_0_12

-- Declarations for this item will be appended below by the statement pipeline.

open scoped HessianLocalNorm

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-
Corollary 5.1.4 lies in the Chapter 5 self-concordance / one-dimensional slice domain.

Sampled owner-style declarations in this domain:
* `IsSelfConcordantOnWith` from `Chap05/Definition_5_1_1`, the chapter owner for
  self-concordance on an open convex domain;
* `hessianLocalNorm` and the notation `‖u‖[f; x]` from `Chap05/Definition_5_1_1`, the canonical
  local norm owner;
* `associatedUnivariateFunctionDomain` from `Chap05/Definition_5_0_12`, the source-facing owner
  for the reciprocal local-norm slice domain.

Best owner abstraction:
* source-facing: the natural parameter domain of the associated univariate reciprocal local-norm
  function along `t ↦ x + t • h`;
* core/canonical: the Hessian local norm `‖h‖[f; x + t • h]`;
* bridge/view: the textbook expansion
  `0 < inner ℝ h ((fderiv ℝ (∇ f) (x + t • h)) h)`.

Primitive data:
* a domain `dom`;
* the self-concordance owner `IsSelfConcordantOnWith dom Mf f`;
* a self-concordant objective `f`;
* a base point `x`;
* a direction `h` with positive local norm at `x`.

Derived API:
* the slice-domain owner `associatedUnivariateFunctionDomain dom f x h`;
* the interval inclusion corollary below, exposed as an owner-level method of
  `IsSelfConcordantOnWith`.

This corollary therefore reuses `associatedUnivariateFunctionDomain` directly as its public owner
and introduces no parallel local slice-domain alias. Its theorem surface follows the surrounding
Chapter 5 owner pattern by living in `namespace IsSelfConcordantOnWith`.
-/

namespace IsSelfConcordantOnWith

-- Proof sketch: restrict `f` to the affine slice `t ↦ x + t • h`. Under the source-faithful
-- positivity hypothesis `0 < (Mf : ℝ) * ‖h‖[f; x]`, self-concordance bounds the derivative of the
-- reciprocal local norm by `Mf`, so the reciprocal local norm stays positive on the displayed
-- interval; equivalently, the associated univariate function remains defined there.
/-- Corollary 5.1.4: if `f` is self-concordant on an open convex domain `dom` and `x ∈ dom`,
then the natural domain of the associated univariate function
`t ↦ (⟪∇² f (x + t • h) h, h⟫)^{-1/2}` contains the interval
`(-1 / (M_f ‖h‖[f; x]), 1 / (M_f ‖h‖[f; x]))` whenever the reciprocal radius is well-defined,
that is, under `0 < (M_f : ℝ) * ‖h‖[f; x]`. -/
theorem associatedUnivariateFunctionDomain_contains_interval
    {dom : Set E} {Mf : NNReal} {f : E → ℝ}
    (hself : IsSelfConcordantOnWith dom Mf f) {x h : E} (hx : x ∈ dom)
    (hMh : 0 < (Mf : ℝ) * ‖h‖[f; x]) :
    Set.Ioo (-(1 / ((Mf : ℝ) * ‖h‖[f; x]))) (1 / ((Mf : ℝ) * ‖h‖[f; x])) ⊆
      associatedUnivariateFunctionDomain dom f x h := sorry

end IsSelfConcordantOnWith

end
