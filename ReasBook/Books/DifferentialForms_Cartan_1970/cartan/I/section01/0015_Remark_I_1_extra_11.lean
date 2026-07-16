import Mathlib
import DifferentialForms_Cartan_1970.cartan.I.section01.«0014_Proposition_7_1»

-- Declarations for this item will be appended below by the statement pipeline.

open scoped PowerSeries
open PowerSeries

universe u

/- Remark I.1-extra-11: in the setup of Proposition 7.1, the left-inverse statement is already
owned by the chapter theorem `powerSeries_subst_right_inverse_is_left_inverse`. -/
recall powerSeries_subst_right_inverse_is_left_inverse {K : Type u} [Field K] {S T : K⟦X⟧}
    (hT0 : T.constantCoeff = 0) (hST : S.subst T = X) :
  T.subst S = X
