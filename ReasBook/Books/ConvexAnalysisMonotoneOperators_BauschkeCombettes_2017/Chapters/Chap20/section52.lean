import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Example_20_52 (from Chap20) -/
open scoped InnerProductSpace SetValuedOperator

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- Example 20.52: for the identity singleton-valued operator, the Fitzpatrick function is the
textbook quadratic map `(x, u) ↦ (1 / 4) * ‖x + u‖ ^ 2`. -/
theorem fitzpatrickFunction_id_apply (x u : H) :
    F[id.toSetValuedOperator] (x, u) = ((1 / 4 : ℝ) * ‖x + u‖ ^ 2 : EReal) := sorry
