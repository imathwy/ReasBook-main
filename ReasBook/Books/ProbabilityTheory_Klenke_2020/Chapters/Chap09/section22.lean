import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_9_22 (from Items/Chap09) -/
universe u v w

/- Definition 9.22: The canonical mathlib notion of the value of a process `X` at a stopping time
`τ` is `MeasureTheory.stoppedValue X τ`. For a finite random time `τ : Ω → ι`, this specializes
to the textbook formula `ω ↦ X (τ ω) ω`. -/
recall MeasureTheory.stoppedValue

/-- For an `ι`-valued finite random time, the stopped value is the textbook pointwise evaluation
`ω ↦ X (τ ω) ω`. -/
-- Proof sketch: Coerce `τ` to a `WithTop ι`-valued map and unfold `MeasureTheory.stoppedValue`.
-- On coerced values, `WithTop.untopA` reduces to the underlying time index, yielding the
-- textbook formula.
theorem stoppedValue_coe_eq_eval
    {Ω : Type u} {ι : Type v} {β : Type w} [Nonempty ι]
    (X : ι → Ω → β) (τ : Ω → ι) :
    MeasureTheory.stoppedValue X (fun ω ↦ (τ ω : WithTop ι)) = fun ω ↦ X (τ ω) ω := rfl
