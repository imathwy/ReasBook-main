import Mathlib.Data.List.TFAE
import StacksProject_2024.Chap10.Definition_10_112_5
import StacksProject_2024.Chap10.Lemma_10_39_18
import StacksProject_2024.Chap15.Definition_15_41_1

-- Declarations for this item will be appended below by the statement pipeline.

open scoped TensorProduct

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

/-- Helper for Lemma 15.41.2 (Regular is a local property): prime-local regularity immediately
implies the maximal-local clause by specialization to maximal points. -/
lemma atMaximals_of_atPrimes (h : AtPrimes f) : AtMaximals f := by
  intro m hm
  -- The maximal-local test is the prime-local test at the underlying prime of `m`.
  simpa using h m.toPrimeSpectrum

/-- Helper for Lemma 15.41.2 (Regular is a local property): regularity at every target prime
implies flatness of the original map by the prime-local flatness criterion. -/
lemma flat_of_atPrimes (h : AtPrimes f) : f.Flat := by
  let _ : Algebra R S := f.toAlgebra
  have hflatModule : Module.Flat R S := by
    rw [flat_iff_flat_localizedModule_atPrime_over_under (R := R) (A := S) (M := S)]
    intro q
    -- View the localized target ring as an algebra over the localized source ring.
    have hqflat :
        (Localization.localRingHom (q.asIdeal.comap f) q.asIdeal f rfl).Flat :=
      (h q).toFlat
    let _ :
        Algebra (Localization.AtPrime (q.asIdeal.comap f)) (Localization.AtPrime q.asIdeal) :=
      RingHom.toAlgebra (Localization.localRingHom (q.asIdeal.comap f) q.asIdeal f rfl)
    have hqflat' :
        (algebraMap (Localization.AtPrime (q.asIdeal.comap f))
          (Localization.AtPrime q.asIdeal)).Flat := by
      simpa [RingHom.algebraMap_toAlgebra] using hqflat
    -- For `M = S`, the localized module is definitionally the localized ring itself.
    simpa using (RingHom.flat_algebraMap_iff.mp hqflat')
  simpa [RingHom.algebraMap_toAlgebra] using
    (RingHom.flat_algebraMap_iff.mpr hflatModule : (algebraMap R S).Flat)

/-- Helper for Lemma 15.41.2 (Regular is a local property): each global fiber is Noetherian once
the target ring `S` is Noetherian. -/
lemma fiber_isNoetherianRing (p : PrimeSpectrum R) :
    let _ : Algebra R S := f.toAlgebra
    IsNoetherianRing (p.asIdeal.Fiber S) := by
  let _ : Algebra R S := f.toAlgebra
  -- Commute the tensor factors so the fiber is viewed as an essentially finite type `S`-algebra.
  let _ : Algebra.EssFiniteType S (S ⊗[R] p.asIdeal.ResidueField) := inferInstance
  let _ : IsNoetherianRing (S ⊗[R] p.asIdeal.ResidueField) :=
    Algebra.EssFiniteType.isNoetherianRing S (S ⊗[R] p.asIdeal.ResidueField)
  exact
    isNoetherianRing_of_ringEquiv (S ⊗[R] p.asIdeal.ResidueField)
      (Algebra.TensorProduct.comm R p.asIdeal.ResidueField S).toRingEquiv.symm

/-- Helper for Lemma 15.41.2 (Regular is a local property): each local fiber ring is Noetherian as
a localization of the corresponding global fiber. -/
lemma fiberLocalRingAt_isNoetherianRing (q : PrimeSpectrum S) :
    let _ : Algebra R S := f.toAlgebra
    IsNoetherianRing (fiberLocalRingAt R S q) := by
  let _ : Algebra R S := f.toAlgebra
  let p : PrimeSpectrum R := PrimeSpectrum.comap f q
  have hp_noetherian : IsNoetherianRing (p.asIdeal.Fiber S) :=
    fiber_isNoetherianRing (f := f) p
  let _ : IsNoetherianRing ((q.asIdeal.under R).Fiber S) := by
    simpa [p, RingHom.algebraMap_toAlgebra] using hp_noetherian
  -- TODO: deduce Noetherianity from the global fiber over `PrimeSpectrum.comap f q` and the
  -- canonical localization presentation `fiberLocalRingAt R S q = A_(fiberPrimeAt q)`.
  -- The local fiber ring is the prime localization of the Noetherian global fiber ring.
  simpa [fiberLocalRingAt] using
    (IsLocalization.isNoetherianRing (fiberPrimeAt R S q).asIdeal.primeCompl
      (fiberLocalRingAt R S q) inferInstance)

/-- Helper for Lemma 15.41.2 (Regular is a local property): the prime localization of the fiber
over `p` corresponding to `q` is exactly the canonical local fiber ring `fiberLocalRingAt R S q`.
-/
lemma fiber_local_ringAt_over_eq
    (p : PrimeSpectrum R) (q : PrimeSpectrum S)
    (hq : PrimeSpectrum.comap f q = p) :
    let _ : Algebra R S := f.toAlgebra
    Algebra.IsGeometricallyRegular p.asIdeal.ResidueField
      (Localization.AtPrime ((PrimeSpectrum.preimageEquivFiber R S p ⟨q, hq⟩).asIdeal)) ↔
      Algebra.IsGeometricallyRegular (q.asIdeal.under R).ResidueField (fiberLocalRingAt R S q) := by
  let _ : Algebra R S := f.toAlgebra
  -- TODO: after the definitional rewrite `simpa [fiberLocalRingAt, fiberPrimeAt, hq]`, the only
  -- remaining gap is a transport between the two residue-field/algebra presentations
  -- `p.asIdeal.ResidueField` and `(q.asIdeal.under R).ResidueField`. This needs a dedicated
  -- bridge lemma comparing the induced `κ(p)`-algebra structure on `fiberLocalRingAt R S q` with
  -- the canonical `fiberLocalRingAtResidueFieldAlgebra`.
  sorry

/-- Helper for Lemma 15.41.2 (Regular is a local property): the closed fiber of the localized map
at `q` is the canonical local fiber ring `fiberLocalRingAt R S q`. -/
lemma fiberLocalRingAt_isGeometricallyRegular_of_localized_isRegularRingMap
    (q : PrimeSpectrum S)
    (h :
      (Localization.localRingHom (q.asIdeal.comap f) q.asIdeal f rfl).IsRegularRingMap) :
    let _ : Algebra R S := f.toAlgebra
    Algebra.IsGeometricallyRegular (q.asIdeal.under R).ResidueField (fiberLocalRingAt R S q) := by
  -- TODO: specialize `h.isGeometricallyRegular_fiber` at the closed point of
  -- `Localization.AtPrime (q.asIdeal.comap f)`, identify its closed fiber with
  -- `fiberLocalRingAt R S q`, and transport the residue field to `κ(q ∩ R)`.
  sorry

/-- Helper for Lemma 15.41.2 (Regular is a local property): prime-local regularity should imply
geometric regularity of each global fiber. -/
lemma geometricallyRegular_fiber_of_atPrimes
    (h : AtPrimes f) (p : PrimeSpectrum R) :
    let _ : Algebra R S := f.toAlgebra
    Algebra.IsGeometricallyRegular p.asIdeal.ResidueField (p.asIdeal.Fiber S) := by
  let _ : Algebra R S := f.toAlgebra
  let _ : IsNoetherianRing (p.asIdeal.Fiber S) := fiber_isNoetherianRing (f := f) p
  -- TODO: package the local fiber-ring data from `h` into the fiberwise localization criterion
  -- for geometric regularity on the now-explicitly Noetherian fiber `p.asIdeal.Fiber S`.
  sorry

/-- Helper for Lemma 15.41.2 (Regular is a local property): regularity is preserved after
localizing the target at a prime. -/
lemma localized_isRegularRingMap (h : f.IsRegularRingMap) (q : PrimeSpectrum S) :
    (Localization.localRingHom (q.asIdeal.comap f) q.asIdeal f rfl).IsRegularRingMap := by
  -- TODO: combine localization of flatness with the fiber-property TFAE for geometric
  -- regularity, after identifying target-prime local fibers of the localized map with the
  -- corresponding `fiberLocalRingAt` of the original map.
  sorry

/-- Helper for Lemma 15.41.2 (Regular is a local property): maximal-local regularity implies the
prime-local clause by localizing once more inside a maximal localization. -/
lemma atPrimes_of_atMaximals (h : AtMaximals f) : AtPrimes f := by
  -- TODO: choose a maximal ideal `m'` containing `q`, apply `h m'`, and then localize that
  -- regular maximal-local map further to recover the prime-local map at `q`.
  sorry

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
    ([ f.IsRegularRingMap, AtPrimes f, AtMaximals f ] : List Prop).TFAE := by
  tfae_have 1 → 2 := by
    intro hreg q
    -- First localize the regular map at the chosen target prime.
    exact localized_isRegularRingMap (f := f) hreg q
  tfae_have 2 → 3 := by
    intro hprimes
    -- Then specialize the prime-local criterion to maximal ideals.
    exact atMaximals_of_atPrimes (f := f) hprimes
  tfae_have 3 → 2 := by
    intro hmax
    -- Route correction: descend from maximal-local data only after reexpressing the prime-local
    -- map as a further localization of a maximal-local map.
    exact atPrimes_of_atMaximals (f := f) hmax
  tfae_have 2 → 1 := by
    intro hprimes
    let _ : Algebra R S := f.toAlgebra
    refine
      { toFlat := flat_of_atPrimes (f := f) hprimes
        isGeometricallyRegular_fiber := ?_ }
    intro p
    -- Recover geometric regularity of each fiber from the local-fiber criterion.
    exact geometricallyRegular_fiber_of_atPrimes (f := f) hprimes p
  tfae_finish

end

end RingHom.IsRegularRingMap
