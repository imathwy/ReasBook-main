import Mathlib
import DifferentialForms_Cartan_1970.I.section01.«frozen_0014_Proposition_7_1»

-- Declarations for this item will be appended below by the statement pipeline.

open scoped PowerSeries
open PowerSeries

universe u

/-- Remark I.1-extra-11: in the setup of Proposition 7.1, a formal substitution right inverse is
also a left inverse, so `T` is the inverse formal series of `S`. -/
-- Proof sketch: derive `S.constantCoeff = 0` and `coeff 1 S ≠ 0` from Proposition 7.1, identify
-- `T` with the canonical inverse via `powerSeries_subst_right_inverse_eq_substInvOfIsUnit`, and
-- then apply the owner theorem `S.subst_substInvOfIsUnit_left`.
theorem powerSeries_subst_right_inverse_is_left_inverse
    {K : Type u} [Field K] {S T : K⟦X⟧}
    (hT0 : T.constantCoeff = 0) (hST : S.subst T = X) :
    T.subst S = X := by
  have hS : S.constantCoeff = 0 ∧ coeff 1 S ≠ 0 := by
    exact (powerSeries_exists_subst_right_inverse_iff).1 ⟨T, hT0, hST⟩
  rw [powerSeries_subst_right_inverse_eq_substInvOfIsUnit hT0 hST]
  exact S.subst_substInvOfIsUnit_left hS.1 (isUnit_iff_ne_zero.2 hS.2)
