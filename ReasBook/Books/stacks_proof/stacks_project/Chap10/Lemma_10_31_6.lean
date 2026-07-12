import Mathlib.RingTheory.Spectrum.Prime.Noetherian
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

variable (R : Type u) [CommSemiring R] [IsNoetherianRing R]

/- Lemma 10.31.6: if `R` is a Noetherian ring, then `Spec(R)` has finitely many irreducible
components. Equivalently, `R` has finitely many minimal prime ideals by
`minimalPrimes.equivIrreducibleComponents` and `minimalPrimes.finite_of_isNoetherianRing`. This
is the canonical theorem `TopologicalSpace.NoetherianSpace.finite_irreducibleComponents` applied
to the canonical instance `PrimeSpectrum.instNoetherianSpace`, and both canonical ingredients are
already available under the weaker assumptions `[CommSemiring R] [IsNoetherianRing R]`. -/
recall TopologicalSpace.NoetherianSpace.finite_irreducibleComponents

end
