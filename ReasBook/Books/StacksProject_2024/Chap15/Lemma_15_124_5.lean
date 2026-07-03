import Mathlib
import StacksProject_2024.Chap10.Lemma_10_50_9
import StacksProject_2024.Chap15.Definition_15_124_1

-- Declarations for this item will be appended below by the statement pipeline.

open IsLocalRing
open IsExtensionOfValuationRings

universe u v

section

variable (A : Type u) [CommRing A] [IsDomain A] [ValuationRing A]
variable {B : Type v} [CommRing B] [Algebra A B] [Algebra.Etale A B]
variable (m : Ideal B) [m.IsPrime] [m.LiesOver (maximalIdeal A)]

local notation "Bₘ" => Localization.AtPrime m

/- Domain-style sampling for Lemma 15.124.5:
- primary domain: étale localizations over valuation rings and the induced weakly unramified
  extension-of-valuation-rings owner;
- sampled owner declarations:
  `IsExtensionOfValuationRings`,
  `IsExtensionOfValuationRings.WeaklyUnramified`,
  `IsLocalization.AtPrime.isLocalRing`,
  `Localization.localRingHom`,
  `IsLocalHom.mk`,
  `map_eq_maximalIdeal_of_exists_etale_away`;
- best owner abstraction: the source-facing main theorem should conclude the canonical owner
  predicate `WeaklyUnramified A Bₘ`, while the localized domain,
  valuation-ring support, and extension-of-valuation-rings structure are supplied by canonical
  localization owners together with the one genuinely new local bridge instance;
- primitive-vs-derived split:
  primitive data: the prime `m` of `B` together with the lying-over condition over `maximalIdeal A`;
  derived API: the local branch fact that `Bₘ` is a domain, the local valuation-ring support on
  `Bₘ`, the local bridge instance `IsExtensionOfValuationRings A Bₘ`, and the
  weakly-unramified conclusion.

Source/core/bridge triage:
- `source-facing`: the weakly unramified branch over `maximalIdeal A`;
- `core/canonical`: `IsExtensionOfValuationRings`, `WeaklyUnramified`, and the canonical
  localization-at-prime algebra;
- `bridge/view`: the canonical instance layer realizing `Bₘ` as the
  canonical target valuation ring over `A`. -/

local instance : IsDomain Bₘ := by
  sorry

local instance : ValuationRing Bₘ := by
  sorry

/-- The canonical map from `A` to the localization at a prime over `maximalIdeal A` is an
extension of valuation rings. -/
instance localizationAtPrime_isExtensionOfValuationRings_of_etale :
    IsExtensionOfValuationRings A Bₘ := by
  sorry

-- Proof sketch: apply the valuation-ring analogue of the étale-local normal Noetherian argument
-- to the localization `B_m`. The prime above `maximalIdeal A` gives the canonical local
-- `A`-algebra structure on `Localization.AtPrime m`; one shows this localization is again a
-- valuation ring, that the induced local map is injective, and that the induced map on value
-- groups is bijective.
/-- Lemma 15.124.5: if `A` is a valuation ring, `A → B` is étale, and `m` is a prime of `B`
lying over the maximal ideal of `A`, then the canonical localized branch `Bₘ` is weakly
unramified over `A`. -/
theorem localizationAtPrime_isWeaklyUnramifiedExtensionOfValuationRings_of_etale :
    WeaklyUnramified A Bₘ := by
  sorry

end
