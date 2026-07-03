import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Note_after_Theorem_8_12 (from Items/Chap08) -/
open MeasureTheory

universe u

variable {Ω : Type u} [MeasurableSpace Ω]
variable {P : Measure Ω} {ℱ : MeasurableSpace Ω}
variable {X Y : Ω → ℝ}

/- Note after Theorem 8.12: equalities involving conditional expectations are interpreted as
almost-sure equalities with respect to the underlying measure. The owner abstraction is
`Filter.EventuallyEq` on the `ae P` filter, written in measure-theoretic notation as
`P[X | ℱ] =ᵐ[P] P[Y | ℱ]`. -/
recall Filter.EventuallyEq

/- The textbook equality of conditional expectations is therefore read in Lean using the canonical
`=ᵐ[P]` notation. -/
#check (P[X | ℱ] =ᵐ[P] P[Y | ℱ])

/-! ### Theorem_8_12 (from Items/Chap08) -/
/- Theorem 8.12 (existence): the source theorem first asserts that the conditional expectation
`E[X | ℱ]` exists. In the chapter's canonical owner-based formalization, that witness is exactly
the mathlib construction `MeasureTheory.condExp`, written `P[X | ℱ]`; Definition 8.11 introduces
this owner object and Lemma 8.10 records its defining textbook properties. -/
recall MeasureTheory.condExp

/- Theorem 8.12 (uniqueness): conditional expectation is unique up to `P`-almost-sure equality.
In the canonical mathlib formulation, this is
`MeasureTheory.ae_eq_condExp_of_forall_setIntegral_eq`, specialized to a probability measure. -/
recall MeasureTheory.ae_eq_condExp_of_forall_setIntegral_eq
