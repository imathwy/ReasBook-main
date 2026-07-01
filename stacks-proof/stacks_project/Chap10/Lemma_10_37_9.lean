import Mathlib.RingTheory.PowerSeries.Ideal
import Mathlib.Tactic.Recall
import stacks_project.Chap10.Definition_10_37_1

-- Declarations for this item will be appended below by the statement pipeline.

open scoped PowerSeries

universe u

variable {R : Type u} [CommRing R]

section

variable [IsNoetherianRing R]

/- Lemma 10.37.9 (Noetherian part): if `R` is a Noetherian normal domain, then `R⟦X⟧` is
Noetherian. This is exactly the canonical mathlib instance on `R⟦X⟧`; the textbook's normality
assumptions are stronger than needed for this part. -/
recall PowerSeries.instIsNoetherianRing

end

section

variable [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R]

/- Layer triage for Lemma 10.37.9:
- the Noetherian statement above is a `core/canonical` recall from mathlib;
- the normal statement below is still `source-facing`, but its owner abstraction is the chapter
  notion `IsIntegrallyClosed` on the power series ring.

The primitive data are exactly the domain, Noetherian, and integrally closed hypotheses on `R`;
normality of `R⟦X⟧` is derived API. -/
/- Lemma 10.37.9 (normal part): if `R` is a Noetherian normal domain, then `R⟦X⟧` is normal.
By Definition 10.37.1, the canonical formulation of this part is the typeclass fact
`IsIntegrallyClosed R⟦X⟧`. -/
-- Proof sketch: write an integral element of the fraction field of `R⟦X⟧` as a Laurent
-- series, use almost integrality over the coefficient ring to show its lowest coefficient lies in
-- `R`, and iterate on higher coefficients to prove every coefficient lies in `R`.
instance : IsIntegrallyClosed R⟦X⟧ := sorry

end
