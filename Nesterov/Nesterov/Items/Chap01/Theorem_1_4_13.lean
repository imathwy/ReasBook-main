import Mathlib.Tactic.Recall
import Nesterov.Chap01.Theorem_1_4_13

-- Declarations for this item will be appended below by the statement pipeline.

/- Theorem 1.4.13 lies in first-order differential calculus and stationarity for local minimizers
on real inner-product spaces.

Relevant owner-style declarations sampled before refining:
* `HasGradientAt`, the canonical owner for stationarity of a differentiable scalar objective;
* `DifferentiableAt.hasGradientAt`, the bridge from differentiability to gradient data;
* `IsLocalMin.fderiv_eq_zero`, mathlib's Fermat theorem for local minima;
* `gradient_eq_zero_of_not_differentiableAt`, which explains why the source-facing equality has no
  differentiability binder;
* `isLocalMin_gradient_eq_zero` in `Chap01/Theorem_1_4_13`, the chapter source-facing theorem for
  this exact statement.

Source/core/bridge triage:
* source-facing: the textbook conclusion `∇ f(xStar) = 0`;
* core/canonical: the stationary witness `HasGradientAt f 0 xStar`;
* bridge/view: the companion owner theorem `isLocalMin_hasGradientAt_zero_of_differentiableAt`.

The previous item file duplicated the chapter theorem with the same public interface and no new
primitive data. This refinement removes that duplicate wheel and keeps the item as a pure recall
surface. -/

recall isLocalMin_gradient_eq_zero
