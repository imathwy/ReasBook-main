import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap01.Text_1_0_11
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap11.Definition_11_3
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap16.Definition_16_1

-- Declarations for this item will be appended below by the statement pipeline.

open scoped InnerProductSpace
universe u

namespace ERealFunction

section Subdifferentials

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

-- Proof sketch: this is the direct bridge between the owner declarations `Argmin`,
-- `SetValuedOperator.zeros`, and `subdifferential`. At slope `0`, the affine-minorant inequality
-- in `mem_subdifferential_iff` is exactly the global minimality condition.
/-- Theorem 16.3: Fermat's rule. The global minimizers of an `]-∞,+∞]`-valued function are exactly
the zeros of its subdifferential. -/
theorem argmin_eq_zeros_subdifferential
    (f : H → Set.Ioi (⊥ : EReal)) :
    Argmin f.asEReal = (∂ f).zeros := by
  ext x
  rw [mem_argmin_iff, isMinOn_univ_iff, SetValuedOperator.mem_zeros_iff, mem_subdifferential_iff]
  constructor <;> intro hx y <;> simpa using hx y

end Subdifferentials

end ERealFunction
