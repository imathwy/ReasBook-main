import Mathlib
import stacks_project.Chap10.Definition_10_162_1
import stacks_project.Chap10.Lemma_10_164_1
import stacks_project.Chap10.Proposition_10_162_15_Nagata

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

section

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]

/-
Domain-style sampling:
* primary domain: smooth descent of the source-facing owner `NagataRing` in commutative algebra;
* sampled owner declarations:
  `NagataRing`,
  `UniversallyJapaneseRing`,
  `nagataRing_iff_universallyJapaneseRing_and_isNoetherianRing`,
  `RingHom.FaithfullyFlat.iff_flat_and_comap_surjective`;
* best owner abstraction: the public conclusion should stay on the source-facing owner
  `NagataRing`, while the map-side hypothesis is canonically organized through
  `RingHom.FaithfullyFlat`, derived here from smoothness plus surjectivity on spectra;
* primitive data vs. derived API: the primitive inputs are `[Algebra.Smooth R S]`, the spectrum
  surjectivity hypothesis, and `[NagataRing S]`; faithful flatness of `algebraMap R S`,
  Noetherianity descent, and the companion owner view `UniversallyJapaneseRing` are derived API.

Source/core/bridge triage:
* `source-facing`: the smooth-descent theorem for `NagataRing`;
* `core/canonical`: `NagataRing`, `UniversallyJapaneseRing`, and `RingHom.FaithfullyFlat`;
* `bridge/view`: `nagataRing_iff_universallyJapaneseRing_and_isNoetherianRing` together with
  `isNoetherianRing_of_faithfullyFlat`.
-/
-- Proof sketch: smooth algebras are flat, so the surjectivity hypothesis on
-- `PrimeSpectrum.comap (algebraMap R S)` upgrades `R → S` to a faithfully flat morphism via
-- `RingHom.FaithfullyFlat.iff_flat_and_comap_surjective`. Lemma `10.164.1` then descends
-- Noetherianity from `S` to `R`, while the chapter bridge
-- `nagataRing_iff_universallyJapaneseRing_and_isNoetherianRing` reduces the remaining work to the
-- universally Japanese part. Since `NagataRing S` already supplies `UniversallyJapaneseRing S`,
-- the source-facing theorem can be assembled through that canonical owner decomposition rather
-- than by rebuilding the `NagataRing` fields directly.
/-- Lemma 10.164.7: if `R → S` is smooth and surjective on spectra, and `S` is a Nagata ring,
then `R` is a Nagata ring. -/
theorem nagataRing_of_smooth_of_specComap_surjective [Algebra.Smooth R S]
    (hsurj : Function.Surjective (PrimeSpectrum.comap (algebraMap R S))) [NagataRing S] :
    NagataRing R := by
  have hff : (algebraMap R S).FaithfullyFlat := by
    rw [RingHom.FaithfullyFlat.iff_flat_and_comap_surjective]
    exact ⟨RingHom.flat_algebraMap_iff.mpr inferInstance, hsurj⟩
  have hNagata :
      NagataRing R ↔ UniversallyJapaneseRing.{u, u} R ∧ IsNoetherianRing R :=
    nagataRing_iff_universallyJapaneseRing_and_isNoetherianRing
  exact
    (hNagata.2
      ⟨by
          letI : UniversallyJapaneseRing.{v, u} S := inferInstance
          sorry,
        isNoetherianRing_of_faithfullyFlat (algebraMap R S) hff⟩)

end
