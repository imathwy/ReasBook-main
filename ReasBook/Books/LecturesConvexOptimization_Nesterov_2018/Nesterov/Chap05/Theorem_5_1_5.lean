import Mathlib
import LecturesConvexOptimization_Nesterov_2018.Chap05.Definition_5_0_13
import LecturesConvexOptimization_Nesterov_2018.Chap05.Definition_5_1_1

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

open scoped HessianLocalNorm DikinEllipsoidNotation

/-
Theorem 5.1.5 belongs to the self-concordance / Dikin-ellipsoid domain.

Sampled owner declarations:
* `hessianLocalNorm` in `Chap05/Definition_5_1_1`, the canonical local Hessian norm;
* `openDikinEllipsoid` together with the notation `W⁰[f; x](r)` in `Chap05/Definition_5_0_13`,
  the Chapter 5 owner for the open local-norm ball;
* `mem_openDikinEllipsoid_iff_hessian_quadratic_lt_sq` in `Chap05/Definition_5_0_14`, the
  textbook quadratic bridge for the same Dikin geometry;
* `IsSelfConcordantOnWith` in `Chap05/Definition_5_1_1`, the chapter owner for quantitative
  self-concordance.

Best owner abstraction:
* source-facing: the open Dikin ellipsoid around `x`;
* core/canonical: `IsSelfConcordantOnWith dom Mf f` together with `‖u‖[f; x]`;
* bridge/view: the membership lemmas for `W⁰[f; x](r)` and its Hessian-quadratic reformulation.

Primitive data:
* a complete real inner-product space `E`;
* a domain `dom`, a function `f`, a self-concordance constant `Mf`, and points `x y : E`.

Derived API:
* the open Dikin ellipsoid `W⁰[f; x](r)`;
* the local displacement norms `‖y - x‖[f; x]` and `‖y - x‖[f; y]`.

This file records the Dikin-ellipsoid and local-norm transport consequences directly as
owner-level methods in `IsSelfConcordantOnWith`, rather than keeping a parallel top-level wrapper
API. -/

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

namespace IsSelfConcordantOnWith

variable {dom : Set E} {Mf : NNReal} {f : E → ℝ}

-- Proof sketch: apply the Dikin ellipsoid inclusion theorem for self-concordant functions. The
-- center hypothesis `hx : x ∈ dom` supplies the standard Dikin radius `1 / M_f`; when `Mf = 0`,
-- that radius is `0`, so `W⁰[f; x](1 / M_f)` is empty and the inclusion is vacuous.
/-- Theorem 5.1.5 (1): if `f` is self-concordant on `dom` with parameter `M_f`, then for every
`x ∈ dom`, the open Dikin ellipsoid `W⁰[f; x](1 / M_f)` is contained in `dom`.
No separate positivity hypothesis on `M_f` is needed. -/
theorem openDikinEllipsoid_inv_constant_subset
    (hself : IsSelfConcordantOnWith dom Mf f) {x : E} (hx : x ∈ dom) :
    W⁰[f; x](1 / (Mf : ℝ)) ⊆ dom := sorry

-- Proof sketch: consider the displacement `h := y - x` and the associated univariate reciprocal
-- local-norm function `t ↦ 1 / ‖h‖_{x + t h}`. The self-concordance differential inequality
-- bounds its slope by `Mf`, and evaluating the resulting estimate between `t = 0` and `t = 1`
-- yields the lower bound after inversion; the same formula remains meaningful when `Mf = 0`.
/-- Theorem 5.1.5 (2): for `x, y ∈ dom`, the local norm of the displacement `y - x` at `y` is at
least `‖y - x‖_x / (1 + M_f ‖y - x‖_x)`. -/
theorem displacement_localNorm_lower_bound
    (hself : IsSelfConcordantOnWith dom Mf f) {x y : E} (hx : x ∈ dom) (hy : y ∈ dom) :
    ‖y - x‖[f; y] ≥ ‖y - x‖[f; x] / (1 + (Mf : ℝ) * ‖y - x‖[f; x]) := sorry

-- Proof sketch: use the same reciprocal local-norm function as in clause (2), but now combine
-- the self-concordance slope bound with the Dikin-radius hypothesis `y ∈ W⁰[f; x](1 / M_f)` to
-- obtain a positive lower bound for the reciprocal at `t = 1`; clause (1) turns that same
-- hypothesis into the derived domain membership `y ∈ dom`, and inverting gives the claimed upper
-- bound. The displayed Dikin-radius hypothesis already rules out the degenerate case `Mf = 0`.
/-- Theorem 5.1.5 (3): if `x ∈ dom` and `y` lies in the open Dikin ellipsoid
`W⁰[f; x](1 / M_f)`, then the local norm of the displacement `y - x` at `y` is at most
`‖y - x‖_x / (1 - M_f ‖y - x‖_x)`. The open-Dikin hypothesis itself excludes the
degenerate case `M_f = 0`, and the domain membership `y ∈ dom` is derived from clause `(1)`. -/
theorem displacement_localNorm_upper_bound
    (hself : IsSelfConcordantOnWith dom Mf f) {x y : E} (hx : x ∈ dom)
    (hxy : y ∈ W⁰[f; x](1 / (Mf : ℝ))) :
    ‖y - x‖[f; y] ≤ ‖y - x‖[f; x] / (1 - (Mf : ℝ) * ‖y - x‖[f; x]) := sorry

end IsSelfConcordantOnWith

end
