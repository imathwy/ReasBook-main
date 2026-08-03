import BauschkeLean.Chap01.Text_1_0_12
import BauschkeLean.Chap20.Proposition_20_22
import BauschkeLean.Chap21.Corollary_21_20

open scoped InnerProductSpace SetValuedOperator

universe u

namespace SetValuedOperator

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

-- Semantic recall note: Chapter 21 already fixes the local-boundedness owner as
-- `SetValuedOperator.IsLocallyBounded`, so this corollary is the inverse/range specialization of
-- that API.
/-- Corollary 21.23: let `A : H → 2^H` be maximally monotone. Then `A` is surjective, i.e.
`A.range = Set.univ`, if and only if `A⁻¹` is locally bounded everywhere on `H`. -/
theorem range_eq_univ_iff_inverse_isLocallyBounded
    (A : SetValuedOperator H H) (hA : Maximal IsMonotone A) :
    A.range = Set.univ ↔ (A⁻¹).IsLocallyBounded := by
  simpa using (isLocallyBounded_iff_dom_eq_univ A⁻¹ (Maximal.inverse hA)).symm

end SetValuedOperator
