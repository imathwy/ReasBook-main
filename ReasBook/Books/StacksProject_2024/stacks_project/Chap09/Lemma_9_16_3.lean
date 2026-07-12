import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open IntermediateField

universe u

variable {F E : Type u} [Field F] [Field E] [Algebra F E]

variable [Algebra.IsAlgebraic F E]

/- Lemma 9.16.3: the canonical field `normalClosure F E (AlgebraicClosure E)` is the normal
closure of `E/F` inside `AlgebraicClosure E`; this is exactly the mathlib theorem
`isNormalClosure_normalClosure`. -/
recall isNormalClosure_normalClosure

/- Companion recall: in `AlgebraicClosure E`, the field
`normalClosure F E (AlgebraicClosure E)` is normal over `F`. -/
recall normalClosure.normal

/- Companion recall: the minimality statement for the normal closure inside `AlgebraicClosure E`
is the canonical theorem `normalClosure_le_iff_of_normal`; applied to the
distinguished copy `(⊥ : IntermediateField E (AlgebraicClosure E)).restrictScalars F`, it says
that a normal intermediate field contains the normal closure exactly when it contains `E`. -/
recall normalClosure_le_iff_of_normal

/- Companion recall: when `E/F` is finite, its normal closure in `AlgebraicClosure E` is finite
over `F`. -/
section

variable [FiniteDimensional F E]

recall normalClosure.is_finiteDimensional

end
