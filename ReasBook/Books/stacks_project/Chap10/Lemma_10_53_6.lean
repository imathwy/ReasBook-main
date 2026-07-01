import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

variable (R : Type u) [CommRing R]

/- Lemma 10.53.6: a commutative ring is Artinian if and only if it has finite length as a module
over itself. This is the canonical theorem `isArtinianRing_iff_isFiniteLength`. -/
recall isArtinianRing_iff_isFiniteLength

section

variable [IsArtinianRing R]

/- An Artinian commutative ring is Noetherian. This is the canonical instance
`instIsNoetherianRingOfIsArtinianRing`. -/
recall instIsNoetherianRingOfIsArtinianRing

/- In an Artinian commutative ring, every prime ideal is maximal. This is the canonical theorem
`IsArtinianRing.isPrime_iff_isMaximal`. -/
recall IsArtinianRing.isPrime_iff_isMaximal

/- An Artinian commutative ring is canonically isomorphic to the finite product of its localizations
at its maximal ideals. This is the canonical equivalence `MaximalSpectrum.toPiLocalizationEquiv`. -/
recall MaximalSpectrum.toPiLocalizationEquiv

end

end
