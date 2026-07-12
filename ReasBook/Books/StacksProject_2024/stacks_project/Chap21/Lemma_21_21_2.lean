import Mathlib.Tactic.Recall
import StacksProject_2024.Chap21.Lemma_21_20_4

namespace RingedSite

/- Domain-style sampling for Lemma 21.21.2:
- primary domain: derived compatibility of localized direct image for localization morphisms of
  ringed sites;
- sampled owner declarations:
  `RingedSite.Hom.localization`,
  `RingedSite.Hom.localizedRestrictionDerived`,
  `RingedSite.Hom.modulePushforwardDerived_localizedRestriction_isIsomorphic`,
  `RingedSite.Hom.modulePushforwardDerived_localizedRestriction_app_isIsomorphic`;
- owner abstraction:
  `source-facing`: the relocalization compatibility of `Rj_*` with further restriction;
  `core/canonical`: the Chapter 21 owner theorem
    `RingedSite.Hom.modulePushforwardDerived_localizedRestriction_isIsomorphic`;
  `bridge/view`: the representable-localization reading of that owner theorem and its objectwise
    companion theorem.

Primitive data are only the canonical localization morphism and the canonical localized
restriction functor. The textbook relocalization statement is exactly the representable-slice
specialization of the existing Chapter 21 owner theorem, so a second local theorem with rebuilt
functor packaging would be duplicate wheel API.
-/

/- Lemma 21.21.2 is the objectwise representable-localization specialization of the Chapter 21
comparison
`RingedSite.Hom.modulePushforwardDerived_localizedRestriction_app_isIsomorphic`. It is the
familiar statement that `(Rf_* E)|_{Y/V}` is canonically isomorphic to `Rg_*(E|_{X/U})` for an
arbitrary morphism of ringed sites, localization object `V`, and derived module `E`. The
theorem-level comparison remains the ambient canonical owner from Lemma `21.20.4`; this file
recalls its source-facing objectwise companion directly. -/
recall Hom.modulePushforwardDerived_localizedRestriction_app_isIsomorphic

end RingedSite
