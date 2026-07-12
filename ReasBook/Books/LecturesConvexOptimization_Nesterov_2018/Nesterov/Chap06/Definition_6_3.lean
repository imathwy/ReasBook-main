import Mathlib.Tactic.Recall
import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open Metric

universe u v

variable {E₁ : Type u} {E₂ : Type v}
  [NormedAddCommGroup E₁] [NormedSpace ℝ E₁]
  [NormedAddCommGroup E₂] [NormedSpace ℝ E₂]

/- Definition 6.3 lies in the operator-norm / dual-pairing domain for dual-valued continuous
linear maps between real normed spaces.

Primary domain:
- operator norms of continuous linear maps `E₁ →L[ℝ] StrongDual ℝ E₂`
- dual-pairing support formulas on unit spheres

Sampled owner-style declarations:
- mathlib `ContinuousLinearMap.opNorm`
- mathlib `ContinuousLinearMap.sSup_sphere_eq_norm`
- project `dual_norm_eq_sSup_closedUnitBall` in `Chap04/Definition_4_4_4`
- project `Seminorm.primalDualOperatorNorm_eq_sSup_dualPairing` and
  `Seminorm.primalDualOperatorNorm_normSeminorm_eq_opNorm` in `Chap02/Definition_2_32`

Best owner abstraction:
- core/canonical: the ambient norm `‖·‖ : (E₁ →L[ℝ] StrongDual ℝ E₂) → ℝ`

Primitive data:
- a continuous linear map `A : E₁ →L[ℝ] StrongDual ℝ E₂`

Derived API:
- the one-sphere norm formula `ContinuousLinearMap.sSup_sphere_eq_norm`
- the two-ball pairing formula from `Seminorm.primalDualOperatorNorm_eq_sSup_dualPairing`
- the textbook two-sphere pairing formula as a source-facing bridge

Source/core/bridge triage:
- source-facing: the textbook max/sup formula over `sphere (0 : E₁) 1 × sphere (0 : E₂) 1`
- core/canonical: `ContinuousLinearMap.opNorm`
- bridge/view: rewriting the canonical norm as the two-sphere dual-pairing supremum

This item is therefore refined so that the main entry is the canonical operator norm owner, while
the textbook two-sphere formula remains only as a companion bridge theorem. -/

/- Definition 6.3: the textbook operator norm `‖A‖_{1,2}` of a dual-valued map
`A : E₁ → E₂*` is the canonical ambient norm on `E₁ →L[ℝ] StrongDual ℝ E₂`. -/
#check (‖·‖ : (E₁ →L[ℝ] StrongDual ℝ E₂) → ℝ)

/- The unit-sphere formula for the codomain norm of `A` is already the canonical mathlib bridge
from the owner `‖A‖` to a source-facing supremum. -/
recall ContinuousLinearMap.sSup_sphere_eq_norm

-- Proof sketch: combine mathlib's one-sphere operator-norm formula for `A` with the chapter's
-- closed-unit-ball dual-norm formula for each `A x`, then pass from closed balls to spheres by
-- radial rescaling and identify the iterated supremum with the supremum over the product of unit
-- spheres.
/-- Companion bridge for Definition 6.3: the canonical operator norm of a dual-valued continuous
linear map is the supremum of the dual pairing over the product of the unit spheres; under the
textbook finite-dimensional hypotheses, this supremum is a maximum. -/
theorem operatorNorm_eq_sSup_dualPairing_unitSpheres (A : E₁ →L[ℝ] StrongDual ℝ E₂) :
    ‖A‖ =
      sSup ((fun xu : E₁ × E₂ ↦ A xu.1 xu.2) ''
        Set.prod (sphere (0 : E₁) 1) (sphere (0 : E₂) 1)) := sorry

end
