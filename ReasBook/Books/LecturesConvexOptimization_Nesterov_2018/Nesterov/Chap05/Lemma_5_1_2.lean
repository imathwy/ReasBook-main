import Mathlib
import LecturesConvexOptimization_Nesterov_2018.Nesterov.Chap05.Definition_5_1_1

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Gradient
open scoped HessianLocalNorm

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-
Lemma 5.1.2 lies in the chapter's self-concordance / higher-derivative multilinear domain.

Sampled owner declarations in this domain:
* `hessian` from `Chap01/Definition_1_4_16`, the chapter owner for the Hessian operator;
* `hessianLocalNorm` and its notation `‖u‖[f; x]` from `Chap05/Definition_5_1_1`;
* `thirdDirectionalDerivative_eq_iteratedFDeriv` from `Chap05/Definition_5_0_10`, the canonical
  bridge from the diagonal third directional derivative to the trilinear third Fréchet derivative;
* `(hessian f x).IsPositive`, the canonical pointwise Hessian-positivity owner used throughout
  Chapter 5 instead of a raw quadratic-form semidefiniteness binder;
* `ContinuousMultilinearMap.le_opNorm`, the canonical multilinear operator-norm estimate in
  mathlib.

Source/core/bridge triage:
* source-facing: the diagonal cubic self-concordance bound;
* core/canonical: the trilinear map `iteratedFDeriv ℝ 3 f x`;
* bridge/view: this equivalence between the diagonal bound and the full trilinear estimate.

Primitive data:
* the objective `f`;
* the domain point `x`;
* the pointwise Hessian positivity owner `(hessian f x).IsPositive`;
* the third Fréchet derivative of `f`.

Derived API:
* the source-facing diagonal bound `|D³f(x)[u, u, u]| ≤ 2 M_f ‖u‖[f; x]^3`;
* the Hessian quadratic-form nonnegativity needed to interpret `‖u‖[f; x]`;
* the full trilinear estimate with respect to the same local norm.

This file keeps the source-facing diagonal statement, but rewrites the public surface through the
chapter owners `hessian`, `thirdDirectionalDerivative`, and `‖u‖[f; x]` instead of duplicating
their raw formulas. The old raw pointwise semidefiniteness binder is replaced by the canonical
owner `(hessian f x).IsPositive`. Since the bridge to `iteratedFDeriv` is pointwise, the domain is
kept open so that `ContDiffOn ℝ 3 f dom` upgrades to `ContDiffAt ℝ 3 f x` for `x ∈ dom`. -/

-- Proof sketch: for the forward direction, apply the norm equality for symmetric trilinear forms
-- on the Hessian-induced inner-product space at each `x` to pass from the diagonal cubic bound to
-- the full multilinear operator-norm bound, then rescale by the three local Hessian norms. For
-- the reverse direction, specialize the trilinear estimate to `u₁ = u₂ = u₃ = u`.
/-- Lemma 5.1.2: for a `C³` function with positive-semidefinite Hessian on an open set `dom`, the
diagonal cubic bound in the definition of `M_f`-self-concordance is equivalent to the full
trilinear estimate on the third derivative. -/
theorem selfConcordant_diagonal_bound_iff_trilinear_bound
    {dom : Set E} {Mf : NNReal} {f : E → ℝ}
    (hdom_open : IsOpen dom)
    (hcont : ContDiffOn ℝ 3 f dom)
    (hH : ∀ {x : E} (hx : x ∈ dom), (hessian f x).IsPositive) :
    (∀ {x : E} (hx : x ∈ dom) (u : E),
      |thirdDirectionalDerivative f x u| ≤
        2 * (Mf : ℝ) * ‖u‖[f; x] ^ (3 : ℕ)) ↔
      ∀ {x : E} (hx : x ∈ dom) (u₁ u₂ u₃ : E),
        |iteratedFDeriv ℝ 3 f x ![u₁, u₂, u₃]| ≤
          2 * (Mf : ℝ) * ‖u₁‖[f; x] * ‖u₂‖[f; x] * ‖u₃‖[f; x] := sorry

namespace IsSelfConcordantOnWith

/-- A self-concordant function satisfies the full trilinear third-derivative estimate on its
domain. -/
theorem iteratedFDeriv_bound
    {dom : Set E} {Mf : NNReal} {f : E → ℝ}
    (hself : IsSelfConcordantOnWith dom Mf f) {x : E} (hx : x ∈ dom) (u₁ u₂ u₃ : E) :
    |iteratedFDeriv ℝ 3 f x ![u₁, u₂, u₃]| ≤
      2 * (Mf : ℝ) * ‖u₁‖[f; x] * ‖u₂‖[f; x] * ‖u₃‖[f; x] := by
  have htrilinear :
      ∀ {y : E} (hy : y ∈ dom) (v₁ v₂ v₃ : E),
        |iteratedFDeriv ℝ 3 f y ![v₁, v₂, v₃]| ≤
          2 * (Mf : ℝ) * ‖v₁‖[f; y] * ‖v₂‖[f; y] * ‖v₃‖[f; y] :=
    (selfConcordant_diagonal_bound_iff_trilinear_bound
      hself.isOpen_domain
      hself.contDiffOn
      fun hx' ↦ hself.hessian_isPositive hx').1
      (fun hx' u ↦ hself.third_deriv_bound hx' u)
  exact htrilinear hx u₁ u₂ u₃

end IsSelfConcordantOnWith
