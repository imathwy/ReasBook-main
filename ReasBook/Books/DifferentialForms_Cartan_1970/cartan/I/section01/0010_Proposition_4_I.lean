import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open scoped PowerSeries

/-
Proposition 4.I is the source-facing specialization of the canonical substitution-composition
theorem `PowerSeries.subst_comp_subst_apply`, with the textbook order hypotheses translated to the
owner predicate `PowerSeries.HasSubst`.
-/
recall PowerSeries.subst_comp_subst_apply

namespace PowerSeries

/-- Proposition 4.I: substitution of univariate formal power series is associative whenever the
two inner series have order at least `1`. -/
-- Proof sketch: translate the order hypotheses to vanishing constant coefficients via
-- `PowerSeries.one_le_order_iff_constCoeff_eq_zero`, obtain the corresponding
-- `PowerSeries.HasSubst.of_constantCoeff_zero'` hypotheses, and apply
-- `PowerSeries.subst_comp_subst_apply`.
theorem subst_assoc_of_one_le_order
    {R : Type u} [CommRing R] (S T U : R⟦X⟧)
    (hT : 1 ≤ T.order) (hU : 1 ≤ U.order) :
    subst U (subst T S) = subst (subst U T) S := by
  simpa using
    subst_comp_subst_apply
      (HasSubst.of_constantCoeff_zero' <|
        one_le_order_iff_constCoeff_eq_zero.mp hT)
      (HasSubst.of_constantCoeff_zero' <|
        one_le_order_iff_constCoeff_eq_zero.mp hU)
      S

end PowerSeries
