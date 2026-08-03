import BauschkeLean.Chap01.Text_1_0_9
import BauschkeLean.Chap01.Text_1_0_13
import BauschkeLean.Chap25.Proposition_25_33

open scoped Pointwise SetValuedOperator

universe u

namespace SetValuedOperator

variable {H : Type u} [AddCommMonoid H] [Module ℝ H]

-- Corollary 25.34 is the doubled-variable specialization of Proposition 25.33, so this file
-- reuses that canonical owner-level identity directly instead of restating it in parallel.

/-- Corollary 25.34: the resolvent of `A + B` is the parallel sum of the doubled resolvents,
precomposed with the doubling homothety. This is the source identity `(25.38)` on the canonical
set-valued-operator surface. -/
theorem resolvent_add_eq_parallelSum_double_resolvents_comp_double
    {A B : SetValuedOperator H H} :
    J[(A + B)] =
      (J[((2 : ℝ) • A)] □ J[((2 : ℝ) • B)]).comp
        ((((2 : ℝ) • (id : H → H)).toSetValuedOperator)) := by
  ext x u
  have hhalf :
      J[((2 : ℝ) • A)] □ J[((2 : ℝ) • B)] =
        (J[(A + B)]).comp ((((1 / 2 : ℝ) • (id : H → H)).toSetValuedOperator)) := by
    simpa [smul_add, smul_smul] using
      parallelSum_resolvent_eq_resolvent_half_smul_add_comp_half_id ℝ
        ((2 : ℝ) • A) ((2 : ℝ) • B)
  simp [hhalf, Function.toSetValuedOperator_apply, smul_smul]

end SetValuedOperator
