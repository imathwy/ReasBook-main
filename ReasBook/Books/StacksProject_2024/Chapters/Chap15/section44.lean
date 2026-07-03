import Mathlib
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Mathlib.RingTheory.RingHom.Etale

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_15_44_1 (from Chap15) -/
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

/-! ### Lemma_15_44_2 (from Chap15) -/
universe u v

section

open Algebra.HasGoingDown

variable {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
variable [Algebra.Etale A B]

/- Domain-style sampling for Lemma 15.44.2:
- primary domain: local commutative algebra of étale maps, prime localizations, and Krull
  dimension;
- sampled owner declarations of the same kind:
  `ringKrullDim_le_of_surjective_comap_of_specializing_or_generalizing`,
  `ringKrullDim_localizationAtPrime_le_of_quasiFiniteAt`,
  `Module.FaithfullyFlat.of_flat_of_isLocalHom`,
  `PrimeSpectrum.comap_surjective_of_faithfullyFlat`;
- owner abstraction: the canonical local rings
  `Localization.AtPrime (q.under A)` and `Localization.AtPrime q`, together with the Chapter 10
  owner inequalities comparing their Krull dimensions;
- primitive data: the étale algebra `A → B` and the prime `q` of `B`;
- derived API: faithful flatness of the induced local map, surjectivity/generalization lifting on
  spectra, and quasi-finiteness at `q`.

Layer triage:
- `source-facing`: equality of the Krull dimensions of the localizations at `q ∩ A` and `q`;
- `core/canonical`: the Chapter 10 owner inequalities on the canonical localizations;
- `bridge/view`: this file specializes those owner inequalities to the étale situation and
  packages them as the textbook equality statement.
-/

-- Proof sketch: this is the specialization of the chapter-10 owner theorems to the étale case.
-- Since an étale algebra is flat, the local map `A_(q ∩ A) → B_q` is flat; because it is also a
-- local map of local rings, it is faithfully flat. Thus `Spec(B_q) → Spec(A_(q ∩ A))` is
-- surjective, and flatness gives going down, so Lemma `10.112.1` yields
-- `dim(A_(q ∩ A)) ≤ dim(B_q)`. Since an étale algebra is quasi-finite at every prime, Lemma
-- `10.125.4` gives the reverse inequality `dim(B_q) ≤ dim(A_(q ∩ A))`.
/-- Lemma 15.44.2: if `A → B` is an étale ring map and `q` is a prime ideal of `B`, then the
local rings `A_(q ∩ A)` and `B_q` have the same Krull dimension. -/
theorem ringKrullDim_localizationAtPrime_eq_of_etale (q : Ideal B) [q.IsPrime] :
    ringKrullDim (Localization.AtPrime (q.under A)) = ringKrullDim (Localization.AtPrime q) := by
  have hAB :
      ringKrullDim (Localization.AtPrime (q.under A)) ≤
        ringKrullDim (Localization.AtPrime q) := by
    letI :
        Module.FaithfullyFlat (Localization.AtPrime (q.under A)) (Localization.AtPrime q) :=
      Module.FaithfullyFlat.of_flat_of_isLocalHom
    simpa using
      ringKrullDim_le_of_surjective_comap_of_specializing_or_generalizing
        (algebraMap (Localization.AtPrime (q.under A)) (Localization.AtPrime q))
        PrimeSpectrum.comap_surjective_of_faithfullyFlat
        (.inr <| iff_generalizingMap_primeSpectrumComap.mp inferInstance)
  have hBA :
      ringKrullDim (Localization.AtPrime q) ≤
        ringKrullDim (Localization.AtPrime (q.under A)) := by
    simpa using ringKrullDim_localizationAtPrime_le_of_quasiFiniteAt q
  exact le_antisymm hAB hBA

end

/-! ### Lemma_15_44_3 (from Chap15) -/
universe u v

open IsLocalRing

section

variable {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
variable [Algebra.Etale A B]

/- Domain-style sampling for Lemma 15.44.3:
- primary domain: regular local rings under étale localization in local commutative algebra;
- sampled owner declarations of the same kind:
  `IsRegularLocalRing`,
  `isRegularLocalRing_of_flat_localHom_of_regularTarget`,
  `isRegularLocalRing_of_flat_localHom_of_regular_closedFiber`,
  `localizationAtPrime_isNoetherianRing_iff_of_etale`;
- owner abstraction: the canonical local rings
  `Localization.AtPrime (q.asIdeal.under A)` and `Localization.AtPrime q.asIdeal`;
- primitive data: the étale algebra `A → B` and the prime `q : PrimeSpectrum B`;
- derived API: Noetherian ascent/descent for the localizations and regularity of the closed fiber
  of the induced local map.

Layer triage:
- `source-facing`: regularity equivalence for the local rings at `q ∩ A` and `q`;
- `core/canonical`: `IsRegularLocalRing` on those two owner localizations;
- `bridge/view`: identifying the closed fiber with a field via the canonical
  `Ideal.Fiber`/quotient comparison for the induced local map.

As in nearby chapter files phrased on localized owners, the prime should be carried by the
canonical point `q : PrimeSpectrum B` rather than by an ideal together with a separate
`[q.IsPrime]` instance. Its contraction `q.asIdeal.under A` is then built into the owner
localizations with no extra public data.
-/
section

variable (q : PrimeSpectrum B)

local notation "Aq" => Localization.AtPrime (q.asIdeal.under A)
local notation "Bq" => Localization.AtPrime q.asIdeal
local notation "ClosedFiber" => Ideal.Fiber (maximalIdeal Aq) Bq

/-- Lemma 15.44.3: if `A → B` is an étale ring map and `q` is a prime of `B`, then the local ring
`A_(q ∩ A)` is regular if and only if the local ring `B_q` is regular. -/
theorem localizationAtPrime_isRegularLocalRing_iff_of_etale :
    IsRegularLocalRing Aq ↔ IsRegularLocalRing Bq := by
  have hnoetherian : IsNoetherianRing Aq ↔ IsNoetherianRing Bq :=
    localizationAtPrime_isNoetherianRing_iff_of_etale q
  have hq_ne_top : q.asIdeal ≠ ⊤ :=
    Ideal.IsPrime.ne_top (inferInstance : q.asIdeal.IsPrime)
  have hEtaleAway : ∃ g : B, g ∉ q.asIdeal ∧ Algebra.Etale A (Localization.Away g) :=
    ⟨1, by simpa [Ideal.ne_top_iff_one] using hq_ne_top, inferInstance⟩
  have hclosedFiber : IsRegularLocalRing ClosedFiber := by
    have hmap : (maximalIdeal Aq).map (algebraMap Aq Bq) = maximalIdeal Bq := by
      rw [← IsLocalization.AtPrime.map_eq_maximalIdeal (q.asIdeal.under A) Aq, Ideal.map_map,
        ← IsScalarTower.algebraMap_eq A Aq Bq]
      simpa using map_eq_maximalIdeal_of_exists_etale_away q.asIdeal hEtaleAway
    let _ : Field (Bq ⧸ maximalIdeal Bq) := Ideal.Quotient.field (maximalIdeal Bq)
    let _ : IsRegularLocalRing (Bq ⧸ maximalIdeal Bq) := inferInstance
    let _ : IsRegularLocalRing (Bq ⧸ (maximalIdeal Aq).map (algebraMap Aq Bq)) :=
      IsRegularLocalRing.of_ringEquiv (Ideal.quotEquivOfEq hmap).symm
    exact isRegularLocalRing_closedFiber_of_quotient
  constructor
  · intro hAq
    let _ : IsRegularLocalRing Aq := hAq
    let _ : IsNoetherianRing Bq := hnoetherian.mp inferInstance
    exact isRegularLocalRing_of_flat_localHom_of_regular_closedFiber hclosedFiber
  · intro hBq
    let _ : IsRegularLocalRing Bq := hBq
    let _ : IsNoetherianRing Aq := hnoetherian.mpr inferInstance
    exact isRegularLocalRing_of_flat_localHom_of_regularTarget Bq

end

end

/-! ### Lemma_15_44_4 (from Chap15) -/
universe u v

/-
Domain-style sampling for Lemma 15.44.4:
- primary domain: étale commutative algebra over Dedekind domains, together with the canonical
  Dedekind-ring and localization owners for one-dimensional normal rings;
- sampled owner declarations of the same kind:
  `IsDedekindRing`,
  `IsDedekindDomain`,
  `normalRing_tfae_isIntegrallyClosed_isFiniteProductOfNormalDomains`,
  `isDedekindDomainByFactorization_iff_isDedekindDomainDvr`,
  `IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain`;
- owner abstraction: the canonical `IsDedekindRing` owner on `B`, the Dedekind-domain owner on
  each product factor, and the localization-at-a-prime owner for the DVR conclusion;
- primitive data: the rings `A`, `B`, the algebra `A → B`, and the étale structure;
- derived API: the finite-product decomposition, the `IsDedekindRing B` bridge, and the
  discrete-valuation-ring conclusion for a nonzero maximal localization.

Layer triage:
- `source-facing`: `exists_finite_product_dedekindDomain_of_etale`;
- `core/canonical`: `IsDedekindRing`, `IsDedekindDomain`, and
  `IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain`;
- `bridge/view`: the local discrete-valuation statement is a source-facing consequence for the
  canonical localization `Localization.AtPrime q.asIdeal`, rather than for an arbitrary chosen
  localization model.

Primitive-vs-derived refinement:
- a Dedekind-domain factor already carries its domain structure, so an extra public witness
  `∀ i, IsDomain (R i)` is redundant;
- the product decomposition is existential source content, so the theorem should keep only the
  Prop-level witness `Nonempty (B ≃+* Π i, R i)` rather than duplicating any extra wrapper API;
- `IsDedekindRing B` is the canonical owner-level conclusion for `B`, so it should be exposed
  directly instead of only through downstream consequences;
- the domain structure on a nonzero maximal localization of `B` is derived local data, so it
  should be internalized as an auxiliary instance rather than exposed in the public statement of
  the DVR theorem.
-/
section

variable {A : Type u} {B : Type v} [CommRing A] [IsDedekindDomain A]
variable [CommRing B] [Algebra A B] [Algebra.Etale A B]

-- Proof sketch: by Lemmas `15.44.2` and `15.44.3`, every localization `B_q` at a maximal ideal
-- has the same dimension and regularity as the corresponding localization of the Dedekind domain
-- `A`, hence is a discrete valuation ring via Algebra, Lemma `10.119.7`. Therefore `B` is a
-- Noetherian normal ring of dimension `1`, and Algebra, Lemmas `10.37.16` and `10.120.17` split
-- it as a finite product of Dedekind domains.
/-- Lemma 15.44.4: if `A → B` is an étale ring map and `A` is a Dedekind domain, then `B` is a
finite product of Dedekind domains. -/
theorem exists_finite_product_dedekindDomain_of_etale :
    ∃ (ι : Type (max u v)) (_ : Finite ι) (R : ι → Type (max u v))
      (_ : ∀ i, CommRing (R i)) (_ : ∀ i, IsDedekindDomain (R i)),
      Nonempty (B ≃+* Π i, R i) := sorry

-- Proof sketch: combine the local dimension comparison of Lemma `15.44.2` and the local
-- regularity equivalence of Lemma `15.44.3` to see that every nonzero maximal localization of `B`
-- is a discrete valuation ring. The canonical owner API then upgrades `B` to an
-- `IsDedekindRing`.
/-- An étale algebra over a Dedekind domain is a Dedekind ring. -/
theorem isDedekindRing_of_etale : IsDedekindRing B := by
  sorry

private instance localizationAtMaximal_isDomain_of_etale
    (q : MaximalSpectrum B) : IsDomain (Localization.AtPrime q.asIdeal) := by
  sorry

-- Proof sketch: combine the previous theorem with the fact that localizing a finite product at a
-- maximal ideal picks out one factor. That factor is a Dedekind domain, and the localization of a
-- Dedekind domain at a nonzero prime is a discrete valuation ring by the standard mathlib theorem
-- `IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain`.
/-- The localization of an étale algebra over a Dedekind domain at a nonzero maximal ideal is a
discrete valuation ring. -/
theorem localizationAtMaximal_isDiscreteValuationRing_of_etale
    (q : MaximalSpectrum B) (hq : q.asIdeal ≠ ⊥) :
    IsDiscreteValuationRing (Localization.AtPrime q.asIdeal) := by
  sorry

end
