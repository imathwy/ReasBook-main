import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Mathlib.RingTheory.RingHom.Etale
import stacks_project.Chap10.Lemma_10_164_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

/-
Domain-style sampling for Lemma 15.44.1:
- primary domain: commutative algebra of étale maps, prime localizations, and Noetherian
  ascent/descent;
- sampled owner declarations: `Localization.AtPrime.algebraOfLiesOver`,
  `Module.FaithfullyFlat.of_flat_of_isLocalHom`, `Algebra.EssFiniteType.of_comp`,
  `Algebra.EssFiniteType.isNoetherianRing`,
  `isNoetherianRing_of_faithfullyFlat`;
- owner abstraction: the induced local map
  `Localization.AtPrime (q.asIdeal.under A) → Localization.AtPrime q.asIdeal`;
- primitive data: the étale algebra `A → B` and the prime `q` of `B`;
- derived API: faithful flatness and essential finite type of the induced local map, giving the
  canonical Noetherian descent and ascent steps;
- layer triage:
  * source-facing: simultaneous Noetherianity of the local rings at a prime of `B` and its
    contraction to `A`;
  * core/canonical: `Algebra.Etale`, `Module.FaithfullyFlat`, and `Algebra.EssFiniteType`;
  * bridge/view: the source prime is canonically `q.asIdeal.under A`, so a separate parameter `p`
    together with `[q.asIdeal.LiesOver p]` is redundant public data.
-/

section

variable {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
variable [Algebra.Etale A B]

-- Proof sketch: étale algebras are smooth, hence flat and of finite presentation. For a prime
-- `q` of `B`, the canonical localized algebra
-- `Localization.AtPrime (q.asIdeal.under A) → Localization.AtPrime q.asIdeal`
-- is local, hence faithfully flat; Noetherianity descends along faithful flatness by Lemma
-- `10.164.1`. The same localized map is essentially of finite type, so Noetherianity also
-- ascends by the canonical essential-finiteness theorem.
/-- Lemma 15.44.1: for an étale ring map `A → B` and a prime `q` of `B`, the localization at the
contracted prime `q ∩ A` is Noetherian if and only if the localization `B_q` is Noetherian. -/
theorem localizationAtPrime_isNoetherianRing_iff_of_etale
    (q : PrimeSpectrum B) :
    IsNoetherianRing (Localization.AtPrime (q.asIdeal.under A)) ↔
      IsNoetherianRing (Localization.AtPrime q.asIdeal) := by
  let R := Localization.AtPrime (q.asIdeal.under A)
  let S := Localization.AtPrime q.asIdeal
  let _ : Algebra R S := inferInstance
  constructor
  · intro hR
    let _ : IsNoetherianRing R := hR
    let _ : Algebra.EssFiniteType R S := Algebra.EssFiniteType.of_comp A R S
    exact Algebra.EssFiniteType.isNoetherianRing R S
  · intro hS
    let _ : IsNoetherianRing S := hS
    let _ : Module.FaithfullyFlat R S := Module.FaithfullyFlat.of_flat_of_isLocalHom
    exact isNoetherianRing_of_faithfullyFlat (algebraMap R S) <| by
      rw [RingHom.faithfullyFlat_algebraMap_iff]
      infer_instance

end
