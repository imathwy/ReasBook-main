import StacksProject_2024.Chap20.Definition_20_47_1
import StacksProject_2024.Chap20.Definition_20_48_1
import StacksProject_2024.Chap20.Perfect_on_opens_ringed_site
import StacksProject_2024.Chap21.Lemma_21_47_4

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.Limits
open RingedSite.Hom
open RingedSite.Hom.ModuleDerived
open TopologicalSpace

noncomputable section

attribute [local instance] HasDerivedCategory.standard

universe u

namespace AlgebraicGeometry.RingedSpace

section

/- Domain-style sampling for Lemma 20.49.5:
- primary domain: perfection, pseudo-coherence, and finite tor dimension in `D(𝒪_X)`;
- sampled owner declarations:
  `DerivedCategory.IsPerfect`,
  `ModuleDerived.IsPseudoCoherent`,
  `ModuleDerived.LocallyHasFiniteTorDimension`,
  `DerivedCategory.isPerfect_iff_opensRingedSiteIsPerfect`,
  `SheafOfModules.RingedSite.isPerfect_iff_isPseudoCoherent_and_locallyHasFiniteTorDimension`;
- best owner abstraction: this file remains source-facing over the Chapter 20 ringed-space owners,
  but its proof surface should be a thin specialization of the Chapter 21 opens-site theorem on
  `opensRingedSite X`, together with explicit bridge theorems for the Chapter 20 pseudo-coherence
  and local finite-Tor-dimension owners.

Source/core/bridge triage:
- `source-facing`: the ringed-space equivalence between perfectness and pseudo-coherence plus local
  finite tor dimension;
- `core/canonical`: `DerivedCategory.IsPerfect`, `IsPseudoCoherent`,
  `ModuleDerived.LocallyHasFiniteTorDimension`;
- `bridge/view`: specialization to `opensRingedSite X` and the bridge theorems below. 
-/

variable {X : RingedSpace.{u}}

variable [HasBinaryProducts (opensRingedSite X).carrier]
variable [HasWeakSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
variable [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{u}]
variable [CategoryWithHomology (Modules X)]
variable [∀ U : Opens X.carrier, MonoidalCategory (moduleDerivedOnOpen X U)]
variable [∀ U : (opensRingedSite X).carrier,
  (localizedRestriction (opensRingedSite X) U).Additive]
variable [∀ U : (opensRingedSite X).carrier,
  PreservesFiniteLimits (localizedRestriction (opensRingedSite X) U)]
variable [∀ U : (opensRingedSite X).carrier,
  PreservesFiniteColimits (localizedRestriction (opensRingedSite X) U)]
variable [∀ U : (opensRingedSite X).carrier,
  CategoryWithHomology (ModuleCat ((opensRingedSite X).localization U))]
variable [∀ U : (opensRingedSite X).carrier,
  MonoidalCategory (RingedSite.Hom.ModuleDerived ((opensRingedSite X).localization U))]

local notation "DMod" => ModuleDerived X
local notation "SiteDMod" => RingedSite.Hom.ModuleDerived (opensRingedSite X)
local notation "SiteIsPseudoCoherent" => (IsPseudoCoherent : SiteDMod → Prop)
local notation "SiteLocallyHasFiniteTorDimension" =>
  (LocallyHasFiniteTorDimension : SiteDMod → Prop)
local notation "SiteIsPerfect" => (IsPerfect : SiteDMod → Prop)

namespace ModuleDerived

/-- The Chapter 20 pseudo-coherence owner agrees with the canonical Chapter 21 pseudo-coherence
owner on the opens ringed site of `X`. -/
theorem isPseudoCoherent_iff_opensRingedSiteIsPseudoCoherent
    (E : DMod) :
    IsPseudoCoherent E ↔ SiteIsPseudoCoherent E := by
  sorry

/-- The Chapter 20 local finite-Tor-dimension owner agrees with the canonical Chapter 21 owner on
the opens ringed site of `X`. -/
theorem locallyHasFiniteTorDimension_iff_opensRingedSiteLocallyHasFiniteTorDimension
    (E : DMod) :
    LocallyHasFiniteTorDimension E ↔ SiteLocallyHasFiniteTorDimension E := by
  sorry

end ModuleDerived

namespace DerivedCategory

/-- Lemma 20.49.5: for an object `E` of `D(𝒪_X)`, perfection is equivalent to
pseudo-coherence together with local finite tor dimension. -/
@[stacks 08CQ]
theorem isPerfect_iff_isPseudoCoherent_and_locallyHasFiniteTorDimension
    (E : DMod) :
    IsPerfect E ↔
      ModuleDerived.IsPseudoCoherent E ∧ E.LocallyHasFiniteTorDimension := by
  letI :
      ∀ U : X.opensRingedSite.carrier, (localizedRestriction X.opensRingedSite U).Additive :=
    inferInstanceAs
      (∀ U : (opensRingedSite X).carrier, (localizedRestriction (opensRingedSite X) U).Additive)
  have hPerfect : IsPerfect E ↔ SiteIsPerfect E := by
    simpa using (DerivedCategory.isPerfect_iff_opensRingedSiteIsPerfect E)
  calc
    IsPerfect E ↔ SiteIsPerfect E := hPerfect
    _ ↔
        SiteIsPseudoCoherent E ∧ SiteLocallyHasFiniteTorDimension E := by
        let E' : SiteDMod := E
        simpa using
          (SheafOfModules.RingedSite.isPerfect_iff_isPseudoCoherent_and_locallyHasFiniteTorDimension
            E')
    _ ↔ ModuleDerived.IsPseudoCoherent E ∧ E.LocallyHasFiniteTorDimension := by
      rw [← ModuleDerived.isPseudoCoherent_iff_opensRingedSiteIsPseudoCoherent E]
      rw [← ModuleDerived.locallyHasFiniteTorDimension_iff_opensRingedSiteLocallyHasFiniteTorDimension
        E]

/-- A perfect object of `D(𝒪_X)` is pseudo-coherent and locally has finite Tor dimension. -/
theorem isPseudoCoherent_and_locallyHasFiniteTorDimension_of_isPerfect
    {E : DMod} (hE : IsPerfect E) :
    ModuleDerived.IsPseudoCoherent E ∧ E.LocallyHasFiniteTorDimension :=
  (isPerfect_iff_isPseudoCoherent_and_locallyHasFiniteTorDimension E).1 hE

/-- A perfect object of `D(𝒪_X)` is pseudo-coherent. -/
theorem isPseudoCoherent_of_isPerfect
    (E : DMod) (hE : IsPerfect E) :
    ModuleDerived.IsPseudoCoherent E :=
  (isPseudoCoherent_and_locallyHasFiniteTorDimension_of_isPerfect hE).1

/-- A perfect object of `D(𝒪_X)` locally has finite tor dimension. -/
theorem locallyHasFiniteTorDimension_of_isPerfect
    (E : DMod) (hE : IsPerfect E) :
    E.LocallyHasFiniteTorDimension :=
  (isPseudoCoherent_and_locallyHasFiniteTorDimension_of_isPerfect hE).2

/-- Pseudo-coherence together with local finite tor dimension implies perfection in `D(𝒪_X)`. -/
theorem isPerfect_of_isPseudoCoherent_of_locallyHasFiniteTorDimension
    (E : DMod) (hpc : ModuleDerived.IsPseudoCoherent E)
    (htor : E.LocallyHasFiniteTorDimension) :
    IsPerfect E :=
  (isPerfect_iff_isPseudoCoherent_and_locallyHasFiniteTorDimension E).2 ⟨hpc, htor⟩

end DerivedCategory

end

end AlgebraicGeometry.RingedSpace
