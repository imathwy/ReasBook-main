import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Example_20_54 (from Chap20) -/
open scoped ContinuousLinearMap ERealFunction InnerProduct InnerProductSpace SetValuedOperator

universe u

namespace ContinuousLinearMap

noncomputable section

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

variable [CompleteSpace H]

/- Source/core/bridge triage:
- `source-facing`: Example 20.54 identifies the Fitzpatrick function of the singleton-valued
  operator induced by a bounded linear map.
- `core/canonical`: the owner abstractions are `F[_]` for Fitzpatrick functions and `q[_]` for
  quadratic potentials.
- `bridge/view`: `A.toSetValuedOperator` is the thin continuous-linear-map bridge to the canonical
  function-level singleton-valued operator owner. -/

-- Proof sketch: expand the Fitzpatrick supremum for the singleton-valued operator induced by `A`.
-- At a graph point `(y, A y)`, the supremand becomes
-- `⟪y, u⟫_ℝ + ⟪x, A y⟫_ℝ - ⟪y, A y⟫_ℝ = 2 * (⟪y, (u + A† x) / 2⟫_ℝ - q[A] y)`.
-- The remaining supremum is exactly twice the conjugate of `q_A` at
-- `(1 / 2) • u + (1 / 2) • A† x`.
/-- Example 20.54: for a bounded linear operator `A`, the Fitzpatrick function of the
singleton-valued operator induced by `A` is `2 q_A^* ((u + A† x) / 2)`. -/
theorem fitzpatrickFunction_eq_two_mul_conjugate_quadraticPotential
    (A : H →L[ℝ] H) (x u : H) :
    F[A.toSetValuedOperator] (x, u) =
      ((2 : ℝ) : EReal) * ((q[A]).toEReal.asEReal∗)
        (((1 / 2 : ℝ) • u) + ((1 / 2 : ℝ) • (A†) x)) := sorry

end

end ContinuousLinearMap
