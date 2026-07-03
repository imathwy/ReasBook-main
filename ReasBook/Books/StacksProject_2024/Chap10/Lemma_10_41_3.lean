import Mathlib.Tactic.Recall
import StacksProject_2024.Chap10.Definition_10_41_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

open PrimeSpectrum

section

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]

/- Domain triage:
* primary domain: going up / going down for the induced map on prime spectra;
* owner abstraction: `Algebra.HasGoingDown R S`;
* sampled canonical declarations:
  `Algebra.HasGoingDown`,
  `Algebra.HasGoingDown.iff_generalizingMap_primeSpectrumComap`,
  `PrimeSpectrum.comap`,
  and the chapter recall shape `SpecializingMap (comap (algebraMap R S))` from
  `Definition_10_41_1`;
* layer: `bridge/view`, since this item only recalls owner-side spectrum-map characterizations and
  adds no new source-facing data.

Primitive-vs-derived split:
* primitive data: none beyond the ambient `R`-algebra structure on `S`.
* derived API: the geometric reformulations `GeneralizingMap (comap (algebraMap R S))` and
  `SpecializingMap (comap (algebraMap R S))`.
-/
/- Lemma 10.41.3 (1): an `R`-algebra `S` satisfies going down if and only if generalizations lift
along the canonical map `Spec S → Spec R`. This is exactly the canonical mathlib theorem
`Algebra.HasGoingDown.iff_generalizingMap_primeSpectrumComap`. -/
recall Algebra.HasGoingDown.iff_generalizingMap_primeSpectrumComap

/- Lemma 10.41.3 (2): Definition 10.41.1 (1) already uses the canonical specializing-map
formulation of going up for the spectrum map `Spec S → Spec R`. -/
#check (SpecializingMap (comap (algebraMap R S)))

end
