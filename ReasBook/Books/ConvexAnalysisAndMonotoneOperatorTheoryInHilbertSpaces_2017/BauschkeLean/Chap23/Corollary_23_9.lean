import BauschkeLean.Chap23.Proposition_23_10

-- Declarations for this item will be appended below by the statement pipeline.

-- Semantic recall note: `lean_leansearch` surfaced only unrelated algebra-spectrum resolvent and
-- generic closure results, so this file follows the verified local Chapter 23 owners `J[...]`,
-- `SetValuedOperator`, and `Maximal IsMonotone`.

open scoped Pointwise SetValuedOperator

universe u

namespace SetValuedOperator

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- Corollary 23.9: a self-map `T : H → H` is firmly nonexpansive if and only if it is the
resolvent of a maximally monotone operator `A : H → 2^H`, expressed as the existence of
`A : SetValuedOperator H H` with `Maximal IsMonotone A` and `J[A] = T.toSetValuedOperator`. -/
theorem firmlyNonexpansive_iff_exists_maximal_isMonotone_resolvent
    (T : H → H) :
    FirmlyNonexpansive T ↔
      ∃ A : SetValuedOperator H H, Maximal IsMonotone A ∧ J[A] = T.toSetValuedOperator := by
  constructor
  · intro hT
    refine ⟨(T.toSetValuedOperator)⁻¹ - id.toSetValuedOperator, ?_, ?_⟩
    · simpa [FirmlyNonexpansive, Function.toSetValuedOperator] using
        (firmlyNonexpansiveOn_and_univ_iff_maximal_sub_id_inverse_ofFunction
          (Set.univ : Set H) (fun x : Set.univ ↦ T x)).mp ⟨hT, rfl⟩
    · simpa [Function.toSetValuedOperator] using
        (resolvent_sub_id_inverse_ofFunction_eq_ofFunction
          (Set.univ : Set H) (fun x : Set.univ ↦ T x))
  · rintro ⟨A, hA, hJ⟩
    have hfirm :
        FirmlyNonexpansiveOn (Set.univ : Set H) (fun x : Set.univ ↦ T x) := by
      exact
        (maximal_isMonotone_iff_firmlyNonexpansiveOn_and_univ_of_resolvent_eq_ofFunction
          A (Set.univ : Set H) (fun x : Set.univ ↦ T x)
          (by simpa [Function.toSetValuedOperator] using hJ)).mp hA |>.1
    simpa [FirmlyNonexpansive] using hfirm

end SetValuedOperator
