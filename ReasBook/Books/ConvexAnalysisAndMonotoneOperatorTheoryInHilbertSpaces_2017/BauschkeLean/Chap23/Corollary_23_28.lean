import BauschkeLean.Chap01.Text_1_0_21
import BauschkeLean.Chap23.Corollary_23_27

open scoped InnerProductSpace Pointwise SetValuedOperator

universe u

namespace SetValuedOperator

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

-- Semantic recall: `lean_leansearch` only surfaced unrelated algebra-spectrum resolvent results,
-- so this corollary uses the verified local operator-reversal owner `Aᵛ` from Text 1.0.21 and
-- the Chapter 23 adjoint-image specialization surface from Corollary 23.27.

/-- The source-facing operator `-Aᵛ` is the adjoint image of `A` under the negative identity
map. -/
theorem neg_reverse_eq_neg_id_adjointImage (A : SetValuedOperator H H) :
    (-Aᵛ : SetValuedOperator H H) = (-ContinuousLinearMap.id ℝ H).adjointImage A := by
  ext x u
  simp [ContinuousLinearMap.adjointImage, SetValuedOperator.reverse]

omit [CompleteSpace H] in
private theorem neg_id_eq_neg_equiv :
    (-ContinuousLinearMap.id ℝ H) =
      ((ContinuousLinearEquiv.neg ℝ : H ≃L[ℝ] H) : H →L[ℝ] H) := by
  ext x
  simp

omit [CompleteSpace H] in
private theorem neg_id_isInvertible : (-ContinuousLinearMap.id ℝ H).IsInvertible := by
  rw [neg_id_eq_neg_equiv]
  exact ContinuousLinearMap.isInvertible_equiv

private theorem neg_id_inverse_eq_adjoint :
    (-ContinuousLinearMap.id ℝ H).inverse = (-ContinuousLinearMap.id ℝ H).adjoint := by
  rw [neg_id_eq_neg_equiv]
  calc
    (((ContinuousLinearEquiv.neg ℝ : H ≃L[ℝ] H) : H →L[ℝ] H)).inverse
        = ((ContinuousLinearEquiv.neg ℝ : H ≃L[ℝ] H)).symm :=
          ContinuousLinearMap.inverse_equiv (ContinuousLinearEquiv.neg ℝ : H ≃L[ℝ] H)
    _ = (-ContinuousLinearMap.id ℝ H).adjoint := by
      ext x
      simp

/-- Corollary 23.28 (1): let `A : H → 2^H` be maximally monotone and set `B = -Aᵛ`, where `Aᵛ`
is the reflected operator `x ↦ A (-x)`. Then `B` is maximally monotone. -/
theorem maximalMonotone_neg_reverse
    {A : SetValuedOperator H H} (hA : Maximal IsMonotone A) :
    Maximal IsMonotone (-Aᵛ : SetValuedOperator H H) := by
  simpa [neg_reverse_eq_neg_id_adjointImage] using
    (Maximal.adjointImage_of_isInvertible_of_inverse_eq_adjoint hA
      (-ContinuousLinearMap.id ℝ H) neg_id_isInvertible neg_id_inverse_eq_adjoint)

/-- Corollary 23.28 (2): let `A : H → 2^H` be maximally monotone and set `B = -Aᵛ`, where `Aᵛ`
is the reflected operator `x ↦ A (-x)`. Then the resolvent satisfies
`J_B = -(J_A)ᵛ`. -/
theorem resolvent_neg_reverse_eq_neg_reverse_resolvent
    (A : SetValuedOperator H H) :
    J[(-Aᵛ : SetValuedOperator H H)] = (-J[A]ᵛ : SetValuedOperator H H) := by
  simpa [neg_reverse_eq_neg_id_adjointImage] using
    (resolvent_adjointImage_eq_adjointImage_resolvent_of_isInvertible_of_inverse_eq_adjoint
      A (-ContinuousLinearMap.id ℝ H) neg_id_isInvertible neg_id_inverse_eq_adjoint)

end SetValuedOperator
