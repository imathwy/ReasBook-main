import Mathlib
import BauschkeLean.Chap01.Text_1_0_11

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Pointwise SetValuedOperator

universe u

namespace SetValuedOperator

variable {H : Type u} [Add H]

/-- Definition 25.29: the parallel sum of operators `A` and `B` from `ℋ` to `2^ℋ` is
`A □ B = (A⁻¹ + B⁻¹)⁻¹`. -/
abbrev parallelSum (A B : SetValuedOperator H H) : SetValuedOperator H H :=
  (A⁻¹ + B⁻¹)⁻¹

scoped[SetValuedOperator] infixl:70 " □ " => SetValuedOperator.parallelSum

open scoped SetValuedOperator

/-- Membership in the parallel sum is equivalent to the defining inverse-of-sum membership
relation. -/
@[simp] theorem mem_parallelSum_iff (A B : SetValuedOperator H H) (x u : H) :
    u ∈ (A □ B) x ↔ x ∈ (A⁻¹ + B⁻¹) u :=
  Iff.rfl

end SetValuedOperator
