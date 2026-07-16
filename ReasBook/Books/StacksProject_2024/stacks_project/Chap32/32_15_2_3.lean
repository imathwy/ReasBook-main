import StacksProject_2024.stacks_project.Chap32.32_15_2_1

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry

universe u

section

variable {X S : Scheme.{u}} {f : X ⟶ S} (sq : ValuativeCommSq f)

/- 32.15.2.3: once the solid valuative diagram from `32.15.2.1` is viewed as its underlying
commutative square, the source claim that no dotted arrow `Spec(A) ⟶ X` exists is exactly the
statement that the canonical type of dotted-arrow lifts is empty. -/
/-- Item 32.15.2.3: for a valuative square, the source statement that there is no dotted arrow
completing the diagram is exactly the emptiness of the canonical type of lifts of the underlying
commutative square. -/
theorem valuativeCommSq_not_hasLift_iff_no_dottedArrow :
    ¬ sq.commSq.HasLift ↔ IsEmpty sq.commSq.LiftStruct := by
  simpa [CommSq.HasLift.iff] using
    (not_nonempty_iff : ¬ Nonempty sq.commSq.LiftStruct ↔ IsEmpty sq.commSq.LiftStruct)

end
