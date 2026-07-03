import Mathlib.Data.List.TFAE
import StacksProject_2024.Chap10.Lemma_10_39_18
import StacksProject_2024.Chap15.Definition_15_41_1

-- Declarations for this item will be appended below by the statement pipeline.

namespace RingHom.IsRegularRingMap

universe u v

section

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]
variable {f : R →+* S} [IsNoetherianRing S]

def AtPrimes (f : R →+* S) : Prop :=
  ∀ q : PrimeSpectrum S,
    (Localization.localRingHom (q.asIdeal.comap f) q.asIdeal f rfl).IsRegularRingMap

def AtMaximals (f : R →+* S) : Prop :=
  ∀ m : MaximalSpectrum S,
    Ideal.IsMaximal (m.asIdeal.comap f) →
      (Localization.localRingHom (m.asIdeal.comap f) m.asIdeal f rfl).IsRegularRingMap

/- Domain sampling pass:
* primary domain: regular ring maps and their local-fiber behavior in commutative algebra;
* sampled owner declarations:
  - `RingHom.IsRegularRingMap f` from `Definition_15_41_1`, the source-facing owner for
    regularity of the ring hom `f`;
  - `Localization.localRingHom (q.asIdeal.comap f) q.asIdeal f rfl`, the canonical owner for the
    induced map `R_(q ∩ R) → S_q`;
  - `flat_iff_flat_localizedModule_atPrime_over_under` from `Lemma_10_39_18`, the canonical
    prime-local flatness criterion for a ring hom after viewing `S` as an `R`-algebra through `f`;
  - `flat_iff_flat_localizedModule_atMaximal_over_under` from `Lemma_10_39_18`, the corresponding
    maximal-local flatness criterion;
  - `IsGeometricallyRegular k A` from `Definition_10_166_2`, the canonical owner for
    geometric regularity of a field algebra.

Source/core/bridge triage:
* `source-facing`: `isRegularRingMap_local_tfae`, the textbook local-property statement for the
  ring map `f`;
* `core/canonical`: `RingHom.IsRegularRingMap f`;
* `bridge/view`: the canonical localized ring hom
  `Localization.localRingHom (q.asIdeal.comap f) q.asIdeal f rfl`, together with the corresponding
  prime-local and maximal-local clauses `AtPrimes f` and `AtMaximals f`.

Primitive data already belong to the owner abstractions `RingHom.IsRegularRingMap f` and
`IsGeometricallyRegular`. This file should therefore keep only the source-facing `TFAE` on the
regular-map owner itself, without a parallel algebra-only wrapper or private clause packaging.
-/

-- Proof sketch: clause `(1)` localizes to clause `(2)`. Conversely, recover flatness of `f`
-- from `flat_iff_flat_localizedModule_atPrime_over_under`, and recover the fiberwise
-- geometric-regularity clause of `RingHom.IsRegularRingMap f` by checking it on all prime
-- localizations of the Noetherian fiber rings. Clause `(3)` is the maximal-ideal version of the
-- same local test, using `flat_iff_flat_localizedModule_atMaximal_over_under` for the flatness
-- part.
/-- Lemma 15.41.2 (Regular is a local property): for a ring map `f : R →+* S` with `S`
Noetherian, the following are equivalent: `f` is regular; for every prime ideal `q ⊂ S`, the
localized map `R_(q ∩ R) → S_q` is regular; and for every maximal ideal `m ⊂ S` whose contraction
to `R` is maximal, the localized map `R_(m ∩ R) → S_m` is regular. -/
theorem isRegularRingMap_local_tfae :
    ([ f.IsRegularRingMap, AtPrimes f, AtMaximals f ] : List Prop).TFAE := sorry

end

end RingHom.IsRegularRingMap
