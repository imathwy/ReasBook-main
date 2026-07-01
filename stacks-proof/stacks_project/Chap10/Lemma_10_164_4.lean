import Mathlib
import stacks_project.Chap10.Definition_10_110_7
import stacks_project.Chap10.Lemma_10_110_9
import stacks_project.Chap10.Lemma_10_164_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

section

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]

/- Domain-style sampling:
* primary domain: faithfully flat descent for regular rings in commutative algebra;
* sampled owner declarations:
  `IsRegularRing`,
  `IsRegularLocalRing`,
  `PrimeSpectrum.comap_surjective_of_faithfullyFlat`,
  `isRegularLocalRing_of_flat_localHom_of_regularTarget`;
* best owner abstraction: the source-facing statement belongs on the chapter owner
  `IsRegularRing`; primewise regular-local descent is derived API from the canonical localized map
  `Localization.AtPrime p.asIdeal → Localization.AtPrime q.asIdeal`, not primitive public data;
* primitive data vs. derived API:
  the primitive inputs are only `f`, `hf`, and `[IsRegularRing S]`;
  the descended Noetherian instance on `R`, the prime `q` over `p`, the localized algebra
  structure, and the flat/local properties of the localized map are all canonical derived data.

Source/core/bridge triage:
* `source-facing`: faithful-flat descent of `IsRegularRing`;
* `core/canonical`: `IsRegularRing`, `IsRegularLocalRing`, and the canonical local map on prime
  localizations;
* `bridge/view`: surjectivity of `PrimeSpectrum.comap` and the local descent theorem
  `isRegularLocalRing_of_flat_localHom_of_regularTarget`.
-/
-- Proof sketch: by Lemma `10.164.1`, faithful flatness descends Noetherianity from `S` to `R`.
-- For each prime `p` of `R`, choose a prime `q` of `S` lying over `p` using surjectivity on
-- spectra for faithfully flat maps. Then `R_p → S_q` is a flat local homomorphism, and `S_q` is a
-- regular local ring because `S` is regular. Lemma `10.110.9` gives that `R_p` is regular local.
-- Since this holds for every prime `p`, the defining condition of `IsRegularRing R` follows.
/-- Lemma 10.164.4: if `f : R →+* S` is faithfully flat and `S` is a regular ring, then `R` is a
regular ring. -/
theorem isRegularRing_of_faithfullyFlat (f : R →+* S) (hf : f.FaithfullyFlat) [IsRegularRing S] :
    IsRegularRing R := by
  letI := f.toAlgebra
  haveI : Module.FaithfullyFlat R S :=
    (RingHom.faithfullyFlat_algebraMap_iff).mp <| by
      simpa [RingHom.algebraMap_toAlgebra] using hf
  letI : IsNoetherianRing R := isNoetherianRing_of_faithfullyFlat f hf
  refine ⟨fun p ↦ ?_⟩
  have hsurj : Function.Surjective (PrimeSpectrum.comap (algebraMap R S)) :=
    PrimeSpectrum.comap_surjective_of_faithfullyFlat
  obtain ⟨q, hq⟩ := hsurj p
  letI : q.asIdeal.LiesOver p.asIdeal := ⟨(congrArg PrimeSpectrum.asIdeal hq).symm⟩
  letI : IsRegularLocalRing (Localization.AtPrime q.asIdeal) :=
    IsRegularRing.isRegularLocalRing_atPrime q
  have halg :
      Localization.localRingHom p.asIdeal q.asIdeal (algebraMap R S) (q.asIdeal.over_def p.asIdeal) =
        algebraMap (Localization.AtPrime p.asIdeal) (Localization.AtPrime q.asIdeal) :=
    Localization.localRingHom_unique _ _ _ _ fun x ↦ by
      rw [← IsScalarTower.algebraMap_apply R S (Localization.AtPrime q.asIdeal) x]
      rw [← IsScalarTower.algebraMap_apply R (Localization.AtPrime p.asIdeal)
          (Localization.AtPrime q.asIdeal) x]
  have hflat :
      (algebraMap (Localization.AtPrime p.asIdeal) (Localization.AtPrime q.asIdeal)).Flat := by
    simpa [halg] using
      (RingHom.Flat.localRingHom hf.flat q.asIdeal p.asIdeal (q.asIdeal.over_def p.asIdeal))
  letI : Module.Flat (Localization.AtPrime p.asIdeal) (Localization.AtPrime q.asIdeal) :=
    (RingHom.flat_algebraMap_iff).mp hflat
  letI : IsLocalHom (algebraMap (Localization.AtPrime p.asIdeal)
      (Localization.AtPrime q.asIdeal)) := by
    simpa [halg] using
      (Localization.isLocalHom_localRingHom p.asIdeal q.asIdeal
        (algebraMap R S) (q.asIdeal.over_def p.asIdeal))
  exact isRegularLocalRing_of_flat_localHom_of_regularTarget (Localization.AtPrime q.asIdeal)

end
