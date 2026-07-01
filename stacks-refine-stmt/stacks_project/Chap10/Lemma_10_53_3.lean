import Mathlib.RingTheory.Artinian.Module
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

universe u

variable {R : Type u} [CommRing R] [IsArtinianRing R]

/- Lemma 10.53.3: if `R` is Artinian, then `R` has only finitely many maximal ideals. The owner
abstraction is `IsArtinianRing R`, and the source-facing conclusion is the derived instance
`Finite (MaximalSpectrum R)` provided by `IsArtinianRing.instFiniteMaximalSpectrum`. -/
recall IsArtinianRing.instFiniteMaximalSpectrum
