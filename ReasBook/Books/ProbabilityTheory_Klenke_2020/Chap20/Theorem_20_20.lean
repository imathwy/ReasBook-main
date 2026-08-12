import Mathlib
import ProbabilityTheory_Klenke_2020.Chap09.Definition_9_7
import ProbabilityTheory_Klenke_2020.Chap20.Theorem_20_19

-- Declarations for this item will be appended below by the statement pipeline.

open Filter MeasureTheory ProbabilityTheory
open scoped BigOperators ProbabilityTheory

noncomputable section

universe u

variable {Ω : Type u}

/-- The event that the Chapter 20 random-walk partial sums of `X` visit `0` infinitely often. -/
def partialSumsReturnToZeroInfinitelyOften (X : ℕ → Ω → ℤ) : Set Ω :=
  {ω | Filter.Frequently (fun n : ℕ ↦ randomWalkPathPartialSum (fun k ↦ X k ω) (n + 1) = 0) atTop}

-- Proof sketch: unfold `partialSumsReturnToZeroInfinitelyOften`; the statement is exactly its
-- defining filter-event formulation.
/- Expanding `partialSumsReturnToZeroInfinitelyOften` gives the event that the `0`-based partial
sums hit `0` for infinitely many times. -/
theorem partialSumsReturnToZeroInfinitelyOften_def (X : ℕ → Ω → ℤ) :
    partialSumsReturnToZeroInfinitelyOften X =
      {ω |
        Filter.Frequently
          (fun n : ℕ ↦ randomWalkPathPartialSum (fun k ↦ X k ω) (n + 1) = 0)
          atTop} := by
  rfl

variable [MeasurableSpace Ω]
variable {P : Measure Ω} [IsProbabilityMeasure P]
variable {X : ℕ → Ω → ℤ}

/- Theorem 20.20 is `source-facing`: it stays on an arbitrary stationary process `X` on `Ω`.
Its canonical owner for the textbook invariant `σ`-algebra `𝒯` is still the shift-invariant
`σ`-algebra `MeasurableSpace.invariants Stream'.tail` on path space. The theorem therefore uses
the thin `bridge/view` obtained by pulling that owner back along the canonical path map
`ω ↦ (n ↦ X n ω)`, rather than introducing a free ambient `σ`-algebra parameter. -/

-- Proof sketch: pull back the canonical shift-invariant `σ`-algebra from path space along the
-- path map `ω ↦ (n ↦ X n ω)`. Stationarity identifies each coordinate `X n` with `X 0` in law, so
-- integrability of `X 0` supplies the coordinatewise integrability needed to apply the
-- ergodic-theoretic recurrence criterion from the previous theorem to the induced stationary path
-- law. Then transfer the resulting almost-sure statement back to the original process.
/-- Theorem 20.20: if `X` is an integer-valued stationary process, the real-valued process
`(fun ω ↦ (X 0 ω : ℝ))` is integrable, and the first coordinate has conditional expectation `0`
with respect to the pullback along the path map `ω ↦ (n ↦ X n ω)` of the invariant `σ`-algebra
`MeasurableSpace.invariants Stream'.tail` of the one-sided shift, then the partial sums return to
`0` infinitely often with probability `1`. Stationarity makes the remaining coordinates
integrable automatically by identical distribution. In the `0`-based indexing used here, the
partial sum at time `n + 1` is `∑_{k < n + 1} X k`. -/
theorem stationary_integer_process_partialSums_returnToZero_infinitelyOften
    (hstationary : IsStationaryProcess X P)
    (hX0_integrable : Integrable (fun ω ↦ (X 0 ω : ℝ)) P)
    (hcentered :
      P[(fun ω ↦ (X 0 ω : ℝ)) |
          MeasurableSpace.comap
            (fun ω ↦ fun n ↦ X n ω)
            (MeasurableSpace.invariants Stream'.tail)] =ᵐ[P] 0) :
    P (partialSumsReturnToZeroInfinitelyOften X) = 1 := sorry
