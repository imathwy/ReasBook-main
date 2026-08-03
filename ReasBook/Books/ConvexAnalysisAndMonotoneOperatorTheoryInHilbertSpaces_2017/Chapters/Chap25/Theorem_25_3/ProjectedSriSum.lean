import BauschkeLean.Chap25.Theorem_25_2

open Set
open ERealFunction
open scoped InnerProductSpace Pointwise SetValuedOperator

universe u

namespace SetValuedOperator

noncomputable section

variable {H : Type u}
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- Helper for Theorem 25.3: this support file re-exports the existing same-space Chapter 25
`sri` sum theorem under the normalized projected-Fitzpatrick owner name used by Theorem 25.3 and
its corollaries. -/
theorem Maximal.add_of_zero_mem_sri_projectedFitzpatrickDifference
    {A B : SetValuedOperator H H} (hA : Maximal IsMonotone A) (hB : Maximal IsMonotone B)
    (hsri : (0 : H) ∈
      sri (Prod.fst '' (ERealFunction.dom (F[A]) - ERealFunction.dom (F[B])))) :
    Maximal IsMonotone (A + B) := by
  -- Route correction: the normalized owner surface already matches Theorem 25.2 exactly, so this
  -- support theorem is only the canonical export bridge expected by Theorem 25.3.
  exact Maximal.add_of_zero_mem_sri_fst_image_dom_fitzpatrick_sub hA hB hsri

end

end SetValuedOperator
