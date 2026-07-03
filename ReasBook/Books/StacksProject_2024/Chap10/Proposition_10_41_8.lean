import Mathlib.RingTheory.Spectrum.Prime.Chevalley
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

section

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]

/- Proposition 10.41.8: if `R → S` is of finite presentation and satisfies going down, then the
induced map `Spec(S) → Spec(R)` is open. The source's flat finite-presentation case is the
immediate specialization obtained from the canonical instance `Algebra.HasGoingDown.of_flat`.
This is exactly the canonical mathlib theorem
`PrimeSpectrum.isOpenMap_comap_of_hasGoingDown_of_finitePresentation`. -/
recall PrimeSpectrum.isOpenMap_comap_of_hasGoingDown_of_finitePresentation

end
