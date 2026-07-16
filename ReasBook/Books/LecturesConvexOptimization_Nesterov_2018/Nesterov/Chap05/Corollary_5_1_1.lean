import LecturesConvexOptimization_Nesterov_2018.Nesterov.Chap05.Definition_5_1_1

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Gradient HessianLocalNorm

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable {dom : Set E} {Mf : NNReal} {f : E → ℝ}

/-
Corollary 5.1.1 lies in the Chapter 5 self-concordance differential-inequality domain.

Sampled owner-style declarations in this domain:
* `hessian` from `Chap01/Definition_1_4_16`, the chapter owner for the Hessian operator;
* `thirdDirectionalDerivative` from `Chap05/Definition_5_0_10`, the source-facing owner for the
  diagonal third derivative;
* `hessianLocalNorm` and the notation `‖u‖[f; x]` from `Chap05/Definition_5_1_1`;
* `IsSelfConcordantOnWith.third_deriv_bound` from `Chap05/Definition_5_1_1`, the chapter owner
  field whose surface this corollary compares with the Hessian-operator inequality.

Source/core/bridge triage:
* source-facing: the textbook equivalence between the cubic self-concordance bound and the Loewner
  operator inequality;
* core/canonical: `hessian`, `thirdDirectionalDerivative`, and `hessianLocalNorm`;
* bridge/view: this corollary translating between those two source-facing formulations.

Primitive data:
* the objective `f`;
* the domain `dom`;
* the self-concordance constant `Mf`.

Derived API:
* the owner hypothesis `IsSelfConcordantOnWith dom Mf f`;
* the operator inequality `fderiv ℝ (hessian f) x u ≤ (2 M_f ‖u‖[f; x]) • hessian f x`.

This file therefore stays at the source-facing corollary layer, but it reuses the chapter owners
instead of restating the same mathematics through raw `iteratedFDeriv`, `Real.sqrt`, and
`fderiv ℝ (∇ f)` formulas. -/

-- Proof sketch: under the standing open-domain, `C³`, and convexity assumptions, the owner
-- `IsSelfConcordantOnWith dom Mf f` is equivalent to its defining cubic bound. Polarize that
-- bound to obtain the quadratic-form estimate for the bilinear form `D³f(x)[u]`, then translate
-- it into Loewner order for the corresponding Hessian-direction operator. Conversely, evaluate
-- the operator inequality on the quadratic form at `u` and `-u` to recover the absolute cubic
-- bound, then rebuild the owner with the standing structural hypotheses.
namespace IsSelfConcordantOnWith

/-- Corollary 5.1.1, forward direction: the Chapter 5 owner `IsSelfConcordantOnWith dom Mf f`
implies the Hessian-direction operator inequality
`D³f(x)[u] ≤ 2 M_f ‖u‖_{∇² f(x)} ∇² f(x)` on `dom`. -/
theorem thirdDerivative_operator_le
    (hself : IsSelfConcordantOnWith dom Mf f) {x : E} (hx : x ∈ dom) (u : E) :
    fderiv ℝ (hessian f) x u ≤
      (2 * (Mf : ℝ) * ‖u‖[f; x]) • hessian f x := by
  sorry

/-- Corollary 5.1.1, converse direction: under the standing open-domain, `C³`, and convexity
assumptions, the Hessian-direction operator inequality reconstructs
`IsSelfConcordantOnWith dom Mf f`. -/
theorem of_thirdDerivative_operator_le
    (h_open : IsOpen dom) (h_contDiff : ContDiffOn ℝ 3 f dom) (h_convexOn : ConvexOn ℝ dom f)
    (hoperator : ∀ ⦃x : E⦄ (_hx : x ∈ dom) (u : E),
      fderiv ℝ (hessian f) x u ≤
        (2 * (Mf : ℝ) * ‖u‖[f; x]) • hessian f x) :
    IsSelfConcordantOnWith dom Mf f := by
  sorry

end IsSelfConcordantOnWith

/-- Corollary 5.1.1: for a thrice continuously differentiable convex function on an open convex
domain, the quantitative self-concordance owner `IsSelfConcordantOnWith dom Mf f` is equivalent
to the Loewner-order bound `D³f(x)[u] ≤ 2 M_f ‖u‖_{∇² f(x)} ∇² f(x)` on the directional
derivative of the Hessian. -/
theorem selfConcordant_iff_thirdDerivative_operator_le
    (h_open : IsOpen dom) (h_contDiff : ContDiffOn ℝ 3 f dom) (h_convexOn : ConvexOn ℝ dom f) :
    IsSelfConcordantOnWith dom Mf f ↔
      ∀ ⦃x : E⦄ (_hx : x ∈ dom) (u : E),
        fderiv ℝ (hessian f) x u ≤
          (2 * (Mf : ℝ) * ‖u‖[f; x]) • hessian f x := by
  constructor
  · intro hself x hx u
    exact hself.thirdDerivative_operator_le hx u
  · intro hoperator
    exact
      IsSelfConcordantOnWith.of_thirdDerivative_operator_le
        h_open h_contDiff h_convexOn hoperator

end
