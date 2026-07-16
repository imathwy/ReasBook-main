import Mathlib.Tactic.Recall
import LecturesConvexOptimization_Nesterov_2018.Nesterov.Chap04.Definition_4_4_4

-- Declarations for this item will be appended below by the statement pipeline.

open Metric

universe u

/- Domain review for this item: it lies in the real continuous-dual / operator-norm domain.

Sampled owner-style declarations:
- mathlib `StrongDual`
- mathlib `ContinuousLinearMap.sSup_unitClosedBall_eq_norm`
- mathlib `IsCompact.exists_sSup_image_eq`
- project `dual_norm_eq_sSup_closedUnitBall` in `Chap04/Definition_4_4_4`

Best owner abstraction:
- source-facing: the textbook dual norm of a real continuous linear functional;
- core/canonical: the existing norm `‖·‖ : StrongDual ℝ E → ℝ`;
- bridge/view: the Chapter 4 support-function formula `dual_norm_eq_sSup_closedUnitBall`.

Primitive data:
- a real normed space `E`;
- a continuous linear functional `g : StrongDual ℝ E`.

Derived API:
- the canonical norm owner `‖g‖`;
- the closed-unit-ball support formula, reused directly from Chapter 4;
- in finite dimensions, existence of a maximizer on the primal closed unit ball.

Source/core/bridge triage:
- source-facing: the dual norm and its finite-dimensional attainment formula;
- core/canonical: the norm on `StrongDual ℝ E`;
- bridge/view: `dual_norm_eq_sSup_closedUnitBall`.

The previous local theorem `dual_norm_eq_sSup_pairing_closedUnitBall` duplicated the exact
Chapter 4 bridge `dual_norm_eq_sSup_closedUnitBall`. This file is therefore recall-first: it
reuses the canonical owner and the existing bridge, and keeps only the new finite-dimensional
attainment statement. -/

section

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

/- Definition 7.6: the dual norm is the canonical norm on the continuous dual `StrongDual ℝ E`.
-/
#check (‖·‖ : StrongDual ℝ E → ℝ)

/- The textbook closed-unit-ball formula is exactly the existing Chapter 4 bridge theorem. -/
recall dual_norm_eq_sSup_closedUnitBall

section

variable [FiniteDimensional ℝ E]

/-- The dual norm of a continuous linear functional is attained on the primal closed unit ball. -/
-- Proof sketch: use compactness of the closed unit ball in finite dimensions and continuity of
-- `x ↦ g x` to obtain a maximizer, then identify the attained supremum with `‖g‖` via
-- `dual_norm_eq_sSup_closedUnitBall`.
theorem dual_norm_exists_maximizer_closedUnitBall (g : StrongDual ℝ E) :
    ∃ x ∈ closedBall (0 : E) 1, ‖g‖ = g x := sorry

end

end
