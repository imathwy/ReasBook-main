import BauschkeLean.Chap22.Theorem_22_18
import BauschkeLean.Chap22.Theorem_22_22

-- Declarations for this item will be appended below by the statement pipeline.

namespace SetValuedOperator

open ERealFunction

-- Semantic recall: `lean_leansearch` surfaced only generic monotonicity lemmas, so the owner/API
-- for this corollary was verified from the local Chapter 22 dependency pair
-- `isMonotone_iff_isCyclicallyMonotone` and
-- `isMaximallyCyclicallyMonotone_iff_eq_subdifferential`.
/-- Corollary 22.23: every maximally monotone set-valued operator `A : ℝ → 2^ℝ` is the
subdifferential of some function `f ∈ Γ₀(ℝ)`. -/
theorem exists_mem_gammaZero_eq_subdifferential_of_isMaximalMonotone
    (A : SetValuedOperator ℝ ℝ) (hA : Maximal IsMonotone A) :
    ∃ f : ℝ → Set.Ioi (⊥ : EReal), f ∈ Γ₀(ℝ) ∧ A = ∂ f := by
  exact
    (isMaximallyCyclicallyMonotone_iff_eq_subdifferential A).mp
      (isMaximallyCyclicallyMonotone_of_isMaximalMonotone hA
        ((isMonotone_iff_isCyclicallyMonotone A).mp hA.1))

end SetValuedOperator
