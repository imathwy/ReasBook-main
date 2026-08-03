import Mathlib
import BauschkeLean.Chap01.Text_1_0_14

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w

namespace SetValuedOperator

section SelectionContinuity

variable {X : Type u} [TopologicalSpace X]
variable {Y : Type v}
variable {Z : Type w} [TopologicalSpace Z]

/-- The canonical continuity predicate for a map defined on the domain of a set-valued operator. -/
def SelectionContinuousAt (A : SetValuedOperator X Y) (T : A.dom → Z) (x : X) : Prop :=
  ∀ hx : x ∈ A.dom, ContinuousAt T ⟨x, hx⟩

/-- Unfolding `SelectionContinuousAt` returns the defining continuity-on-the-domain statement. -/
theorem selectionContinuousAt_iff
    (A : SetValuedOperator X Y) (T : A.dom → Z) (x : X) :
    SelectionContinuousAt A T x ↔
      ∀ hx : x ∈ A.dom, ContinuousAt T ⟨x, hx⟩ :=
  Iff.rfl

end SelectionContinuity

end SetValuedOperator
