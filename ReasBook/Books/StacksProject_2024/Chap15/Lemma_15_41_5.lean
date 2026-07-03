import Mathlib
import stacks_project.Chap10.Lemma_10_147_5
import stacks_project.Chap15.Definition_15_41_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

namespace RingHom

section

variable {R : Type u} {S : Type v}
variable [CommRing R] [CommRing S]
variable {f : R →+* S}

/- Domain sampling pass:
* primary domain: regular ring maps and filtered colimits of smooth commutative algebras;
* sampled owner declarations:
  - `RingHom.IsFilteredColimitOfSmooth` from `Lemma_10_147_5`, the source-facing owner for the
    intrinsic hypothesis that a ring map `R →+* S` is a filtered colimit of smooth `R`-algebras;
  - `RingHom.IsRegularRingMap` from `Definition_15_41_1`, the source-facing owner for regularity;
  - `Algebra.isGeometricallyRegular_of_smooth` from `Lemma_10_166_4`, the canonical smooth-to-
    geometric-regularity owner used on field-valued fibers;
  - the inherited `RingHom.Flat` data inside `RingHom.IsRegularRingMap` from
    `Definition_15_41_1`, showing that flatness is primitive owner data rather than a separate
    local wrapper.

Source/core/bridge triage:
* `source-facing`: `isRegularRingMap_of_noetherianFibers`;
* `core/canonical`: `RingHom.IsFilteredColimitOfSmooth` together with
  `RingHom.IsRegularRingMap`, both owned by the ring hom `f`;
* `bridge/view`: any chosen directed-system presentation of the codomain of `f`, together with
  the hidden same-universe presentation inside `RingHom.IsFilteredColimitOfSmooth`.

Primitive data for the hypothesis are only that the ring map `f` is a filtered colimit of smooth
`R`-algebras. A chosen indexing type, stage family, and direct-limit model are auxiliary
presentation data already packaged by `RingHom.IsFilteredColimitOfSmooth`, so they should not
remain the main public API here.
-/

-- Proof sketch: choose a filtered diagram of smooth `R`-algebras presenting `f`. Lemma `10.39.3`
-- gives flatness of `f`. For a prime `p ⊂ R` and a finite purely inseparable extension
-- `κ(p) ⊂ k`, Lemma `10.137.3` identifies `k ⊗[R] S` with the filtered colimit of the corresponding
-- smooth `k`-algebras, hence of regular local rings by Lemma `10.140.3`; the Noetherianity
-- hypothesis on the fibers then lets Lemma `10.106.8` promote those colimit local rings to
-- regular ones, giving geometric regularity of every fiber and therefore regularity of `f`.
/-- Lemma 15.41.5: if a ring map `f : R →+* S` is a filtered colimit of smooth `R`-algebras and
every fiber ring `p.asIdeal.Fiber S = κ(p) ⊗[R] S` is Noetherian, then `f` is regular. -/
theorem IsFilteredColimitOfSmooth.isRegularRingMap_of_noetherianFibers
    (hcolim : f.IsFilteredColimitOfSmooth)
    (hfiber_noetherian :
      let _ : Algebra R S := f.toAlgebra
      ∀ p : PrimeSpectrum R, IsNoetherianRing (p.asIdeal.Fiber S)) :
    f.IsRegularRingMap := by
  let _ : Algebra R S := f.toAlgebra
  sorry

end

end RingHom
