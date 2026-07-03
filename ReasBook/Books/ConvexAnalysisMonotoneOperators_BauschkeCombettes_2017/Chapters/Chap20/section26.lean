import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Example_20_26 (from Chap20) -/
open scoped InnerProductSpace Pointwise
open ERealFunction

universe u

namespace Set

section

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

-- Proof sketch: show that the indicator `ι_C` belongs to `Γ₀(H)` for a nonempty closed convex set
-- `C`, apply Moreau's theorem `subdifferential_isMaximallyMonotone_of_mem_gammaZero` to `ι_C`, and
-- then rewrite the resulting operator with `subdifferential_setIndicator_eq_normalCone`.
/-- Example 20.26: for a nonempty closed convex subset `C` of a real Hilbert space, the normal
cone operator `N[C]` is maximally monotone. -/
theorem normalCone_isMaximallyMonotone_of_nonempty_isClosed_convex
    {C : Set H} (hC_nonempty : C.Nonempty) (hC_closed : IsClosed C) (hC_convex : Convex ℝ C) :
    Maximal SetValuedOperator.IsMonotone (N[C]) := by
  have hindicator : ι[C] ∈ Γ₀(H) :=
    indicator_mem_gammaZero_of_nonempty_isClosed_convex hC_nonempty hC_closed hC_convex
  simpa [subdifferential_setIndicator_eq_normalCone C hC_nonempty] using
    subdifferential_isMaximallyMonotone_of_mem_gammaZero hindicator

end

end Set
