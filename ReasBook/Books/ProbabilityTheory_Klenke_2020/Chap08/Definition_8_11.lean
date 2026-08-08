import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open scoped MeasureTheory ProbabilityTheory

universe u

variable {Ω : Type u} {m0 m : MeasurableSpace Ω}

/- Definition 8.11: Conditional expectation with respect to a sub-σ-algebra is the canonical
mathlib object `P[X | m]`. -/
recall MeasureTheory.condExp

/- Conditional probabilities of events with respect to a sub-σ-algebra are a derived notation,
not a second owner construction: `P⟦B | m⟧` abbreviates the conditional expectation of the
indicator of `B`, namely `MeasureTheory.condExp m P (Set.indicator B fun _ ↦ (1 : ℝ))`. -/
variable (P : Measure[m0] Ω) (B : Set Ω)

#check P⟦B | m⟧
