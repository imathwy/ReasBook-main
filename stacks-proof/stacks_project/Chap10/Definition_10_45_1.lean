import Mathlib.Algebra.Field.ULift
import Mathlib.FieldTheory.PurelyInseparable.PerfectClosure
import Mathlib.Tactic.Recall
import stacks_project.Chap10.Definition_10_42_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

section

variable {k : Type u} [Field k]

/- Definition 10.45.1: the canonical owner abstraction for a perfect field is the mathlib class
`PerfectField`. -/
recall PerfectField

/-- Definition 10.45.1, source-facing bridge: a field `k` is perfect if and only if every field
extension `K / k` is separable in the Stacks Project sense of Definition `10.42.1 (2)`. -/
theorem perfectField_iff_forall_isSeparableOver :
    PerfectField k ↔
      ∀ (K : Type (max u v)) [Field K] [Algebra k K], Algebra.IsSeparableOver k K := by
  constructor
  · intro hk K _ _
    letI : PerfectField k := hk
    infer_instance
  · intro h
    have hClosure : Algebra.IsSeparableOver k (ULift.{v} (AlgebraicClosure k)) := h _
    have hClosure' : Algebra.IsSeparableOver k (AlgebraicClosure k) :=
      hClosure.of_algEquiv ULift.algEquiv
    exact (perfectField_iff_isSeparable_algebraicClosure k (AlgebraicClosure k)).2
      hClosure'.isSeparable

end
