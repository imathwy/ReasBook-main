import Mathlib
import BauschkeLean.Chap04.Remark_4_34
import BauschkeLean.Chap04.Text_4_21_1
import BauschkeLean.Chap20.Example_20_30

-- Declarations for this item will be appended below by the statement pipeline.

open scoped InnerProductSpace

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

section

variable {C : Set H} (hC_nonempty : C.Nonempty) (hC_closed : IsClosed C) (hC_convex : Convex ℝ C)

local notation "hC" =>
  isChebyshev_of_nonempty_isClosed_convex hC_nonempty hC_closed hC_convex

-- Proof sketch: Proposition 4.16 shows that the metric projection `P[C, hC]` onto a nonempty closed
-- convex set is firmly nonexpansive. By Remark 4.34, this is equivalent to `1 / 2`-averagedness,
-- and Example 20.30 then yields maximal monotonicity of the associated singleton-valued operator.
/-- Example 20.32: the metric projection onto a nonempty closed convex subset of a real Hilbert
space is maximally monotone when viewed as its associated singleton-valued set-valued operator. -/
theorem projectionPoint_toSetValuedOperator_isMaximallyMonotone_of_nonempty_isClosed_convex :
    Maximal SetValuedOperator.IsMonotone (P[C, hC]).toSetValuedOperator := by
  exact Function.toSetValuedOperator_isMaximallyMonotone_of_averaged_le_half
    ((firmlyNonexpansive_iff_averaged_half).mp
      (firmlyNonexpansive_projectionPoint_of_nonempty_isClosed_convex
        hC_nonempty hC_closed hC_convex))
    le_rfl

end
