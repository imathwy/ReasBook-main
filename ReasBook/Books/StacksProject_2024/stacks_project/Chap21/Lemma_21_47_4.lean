import StacksProject_2024.Chap21.Definition_21_45_1
import StacksProject_2024.Chap21.Definition_21_46_1
import StacksProject_2024.Chap21.Definition_21_47_1

open CategoryTheory
open CategoryTheory.Limits
open RingedSite.Hom
open RingedSite.Hom.ModuleDerived

noncomputable section

universe u v

attribute [local instance] HasDerivedCategory.standard

set_option checkBinderAnnotations false

namespace SheafOfModules.RingedSite

section

/- Domain-style sampling for Lemma 21.47.4:
- primary domain: perfection, pseudo-coherence, and local finite Tor dimension in the derived
  category of modules on a ringed site;
- sampled owner declarations:
  `RingedSite.Hom.ModuleDerived.IsPseudoCoherent`,
  `RingedSite.Hom.ModuleDerived.LocallyHasFiniteTorDimension`,
  `RingedSite.Hom.ModuleDerived.IsPerfect`,
  `RingedSite.Hom.ModuleDerived`;
- best owner abstraction: this theorem should reuse the Chapter 21 owner predicates
  `E.IsPerfect`, `E.IsPseudoCoherent`, and `E.LocallyHasFiniteTorDimension` on the ambient
  ringed site `X`, rather than rebuilding local pseudo-coherence predicates from a chosen
  restriction functor;
- primitive data: the ambient ringed site `X` and an object `E : ModuleDerived X`;
- derived API: the equivalence between perfectness and pseudo-coherence plus local finite Tor
  dimension below.

Source/core/bridge triage:
- `source-facing`: the equivalence theorem below;
- `core/canonical`: `E.IsPseudoCoherent`, `E.LocallyHasFiniteTorDimension`,
  `E.IsPerfect`, and `ModuleDerived X`;
- `bridge/view`: the duplicate local pseudo-coherence API formerly in this file, now deleted in
  favor of `Definition_21_45_1`. -/

variable {X : RingedSite.{u, v}}

local notation "Mod" => ModuleCat X
local notation "DMod" => ModuleDerived X

variable [HasBinaryProducts X.carrier]
variable [CategoryWithHomology Mod]
variable [∀ U : X, CategoryWithHomology (ModuleCat (X.localization U))]
variable [∀ U : X, MonoidalCategory (ModuleDerived (X.localization U))]
variable [∀ U : X, (localizedRestriction X U).Additive]
variable [∀ U : X, PreservesFiniteLimits (localizedRestriction X U)]
variable [∀ U : X, PreservesFiniteColimits (localizedRestriction X U)]

-- Proof sketch: combine Lemma `21.47.3`, which gives perfectness from pseudo-coherence together
-- with a fixed tor-amplitude interval, with Definition `21.46.1`, which supplies such an interval
-- locally on a cover. The converse follows by combining the local strictly perfect description of
-- Definition `21.47.1` with the evident pseudo-coherence and finite-Tor-dimension consequences on
-- each member of a cover.
/-- Lemma 21.47.4: for an object `E` of `D(𝒪_X)` on a ringed site, `E` is perfect if and only if
it is pseudo-coherent and locally has finite Tor dimension. -/
@[stacks 08G8]
theorem isPerfect_iff_isPseudoCoherent_and_locallyHasFiniteTorDimension
    (E : DMod) :
    E.IsPerfect ↔ E.IsPseudoCoherent ∧ E.LocallyHasFiniteTorDimension := by
  sorry

/-- A perfect object of `D(𝒪_X)` is pseudo-coherent and locally has finite Tor dimension. -/
theorem isPseudoCoherent_and_locallyHasFiniteTorDimension_of_isPerfect
    {E : DMod} (_ : E.IsPerfect) :
    E.IsPseudoCoherent ∧ E.LocallyHasFiniteTorDimension := by
  exact
    (isPerfect_iff_isPseudoCoherent_and_locallyHasFiniteTorDimension E).1 ‹E.IsPerfect›

/-- A perfect object of `D(𝒪_X)` is pseudo-coherent. -/
theorem isPseudoCoherent_of_isPerfect
    {E : DMod} (_ : E.IsPerfect) :
    E.IsPseudoCoherent := by
  exact (isPseudoCoherent_and_locallyHasFiniteTorDimension_of_isPerfect ‹E.IsPerfect›).1

/-- A perfect object of `D(𝒪_X)` locally has finite Tor dimension. -/
theorem locallyHasFiniteTorDimension_of_isPerfect
    {E : DMod} (_ : E.IsPerfect) :
    E.LocallyHasFiniteTorDimension := by
  exact (isPseudoCoherent_and_locallyHasFiniteTorDimension_of_isPerfect ‹E.IsPerfect›).2

/-- An object of `D(𝒪_X)` is perfect once it is pseudo-coherent and locally has finite Tor
dimension. -/
theorem isPerfect_of_isPseudoCoherent_of_locallyHasFiniteTorDimension
    {E : DMod} (_ : E.IsPseudoCoherent) (_ : E.LocallyHasFiniteTorDimension) :
    E.IsPerfect := by
  exact
    (isPerfect_iff_isPseudoCoherent_and_locallyHasFiniteTorDimension E).2
      ⟨‹E.IsPseudoCoherent›, ‹E.LocallyHasFiniteTorDimension›⟩

end

end SheafOfModules.RingedSite
