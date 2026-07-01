import Mathlib
import stacks_project.Chap15.Situation_15_6_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Limits TopCat

universe u

noncomputable section

variable {B A A' : Type u} [CommRing B] [CommRing A] [CommRing A']

/- Domain-style sampling for 15.6.2:
- primary domain: prime-spectrum maps in `TopCat` and pushout squares in `CategoryTheory`;
- sampled owner declarations:
  `PrimeSpectrum.comap`,
  `PrimeSpectrum.continuous_comap`,
  `IsPushout`,
  `IsPushout.exists_desc`;
- best owner abstraction: the primitive source-facing data is still
  `S : SurjectiveRingPullbackSituation B A A'`; the induced maps on prime spectra are derived from
  the canonical owner `PrimeSpectrum.comap`, and the universal-property claim is owned by
  `IsPushout`;
- primitive data: the ring maps and surjectivity hypothesis stored in `S`;
- derived API: the topological-space object `S.specBprime` and the four canonical spectrum maps
  `S.specToB`, `S.specToAprime`, `S.specBToBprime`, and `S.specAprimeToBprime`.

Source/core/bridge triage:
- `source-facing`: the pushout statement for the spectrum square of Situation `15.6.1`;
- `core/canonical`: `PrimeSpectrum.comap`, `PrimeSpectrum.continuous_comap`, and `IsPushout`;
- `bridge/view`: the induced `TopCat` morphisms attached to `S`. -/

namespace SurjectiveRingPullbackSituation

variable (S : SurjectiveRingPullbackSituation B A A')

/-- The topological space `Spec(B')` attached to a surjective ring pullback situation. -/
abbrev specBprime : TopCat :=
  TopCat.of (PrimeSpectrum S.Bprime)

/-- The canonical map `Spec(A) → Spec(B)` induced by `B → A`. -/
abbrev specToB : TopCat.of (PrimeSpectrum A) ⟶ TopCat.of (PrimeSpectrum B) :=
  TopCat.ofHom ⟨PrimeSpectrum.comap S.toA, PrimeSpectrum.continuous_comap S.toA⟩

/-- The canonical map `Spec(A) → Spec(A')` induced by `A' → A`. -/
abbrev specToAprime : TopCat.of (PrimeSpectrum A) ⟶ TopCat.of (PrimeSpectrum A') :=
  TopCat.ofHom ⟨PrimeSpectrum.comap S.fromAprime, PrimeSpectrum.continuous_comap S.fromAprime⟩

/-- The canonical map `Spec(B) → Spec(B')` induced by `B' → B`. -/
abbrev specBToBprime : TopCat.of (PrimeSpectrum B) ⟶ S.specBprime :=
  TopCat.ofHom ⟨PrimeSpectrum.comap S.bprimeToB, PrimeSpectrum.continuous_comap S.bprimeToB⟩

/-- The canonical map `Spec(A') → Spec(B')` induced by `B' → A'`. -/
abbrev specAprimeToBprime : TopCat.of (PrimeSpectrum A') ⟶ S.specBprime :=
  TopCat.ofHom ⟨PrimeSpectrum.comap S.bprimeToAprime, PrimeSpectrum.continuous_comap S.bprimeToAprime⟩

end SurjectiveRingPullbackSituation

-- Proof sketch: let `B'` be the categorical pullback of `B → A ← A'`. The two projection maps
-- `B' → B` and `B' → A'` induce a cocone `Spec(B) ← Spec(A) → Spec(A') ⟶ Spec(B')`. The
-- textbook proof shows that the induced map from the topological pushout to `Spec(B')` is
-- bijective, separating primes according to whether they contain `ker(A' → A)`, and then proves
-- openness of this map by the localization argument using Lemma `15.5.3`.
/-- Lemma 15.6.2: in a surjective ring pullback situation, the prime spectrum of the fibre product
ring `B ×_A A'` is the pushout of `Spec(B) ← Spec(A) → Spec(A')` in the category of topological
spaces. -/
theorem spec_pullback_of_surjective_isPushout
    (S : SurjectiveRingPullbackSituation B A A') :
    IsPushout S.specToB S.specToAprime S.specBToBprime S.specAprimeToBprime := sorry

end
