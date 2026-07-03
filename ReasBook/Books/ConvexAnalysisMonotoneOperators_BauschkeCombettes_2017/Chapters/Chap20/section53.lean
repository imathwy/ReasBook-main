import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Example_20_53 (from Chap20) -/
open scoped InnerProductSpace SetValuedOperator

universe u

namespace ContinuousLinearMap

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

-- Proof sketch: expand the Fitzpatrick supremum for the singleton-valued operator induced by `A`.
-- At a graph point `(y, A y)`, the skew-adjoint hypothesis forces `⟪y, A y⟫_ℝ = 0`, so the
-- supremand becomes `⟪y, u - A x⟫_ℝ`. If `u = A x`, every term is `0`; if `u ≠ A x`, choose `y`
-- along `u - A x` to make the supremum equal `⊤`. This is exactly the graph indicator.
/-- Example 20.53: if `A.adjoint = -A`, then the Fitzpatrick function of the singleton-valued
operator induced by `A` is the extended-real indicator of its graph. -/
theorem fitzpatrickFunction_eq_indicator_graph_of_adjoint_eq_neg
    (A : H →L[ℝ] H) (hA : A.adjoint = -A) :
    F[A.toSetValuedOperator] =
      (ι[gra A.toSetValuedOperator]).asEReal := sorry

end ContinuousLinearMap
