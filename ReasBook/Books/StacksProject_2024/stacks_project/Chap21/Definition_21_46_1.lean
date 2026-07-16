import StacksProject_2024.stacks_project.Chap21.Definition_21_46_1_Core
import StacksProject_2024.stacks_project.Chap21.Lemma_21_20_4

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open scoped RingedSiteDerived
noncomputable section

universe u v

attribute [local instance] HasDerivedCategory.standard

set_option checkBinderAnnotations false
open RingedSite.Hom

namespace RingedSite.Hom.ModuleDerived

open SheafOfModules.RingedSite

section

variable {X : RingedSite.{u, v}}

local notation "DMod" => ModuleDerived X

variable [HasBinaryProducts X.carrier]
variable [CategoryWithHomology (ModuleCat X)]
variable [∀ U : X, CategoryWithHomology (ModuleCat (X.localization U))]
variable [∀ U : X, MonoidalCategory (ModuleDerived (X.localization U))]
variable [∀ U : X, (localizedRestriction X U).Additive]
variable [∀ U : X, PreservesFiniteLimits (localizedRestriction X U)]
variable [∀ U : X, PreservesFiniteColimits (localizedRestriction X U)]

/- Domain-style sampling for Definition 21.46.1 (local layer):
- primary domain: local finite tor dimension in the derived category of modules on a ringed site;
- sampled owner declarations:
  `RingedSite.Hom.ModuleDerived.LocallyHasFiniteTorDimension`,
  `SheafOfModules.RingedSite.HasFiniteTorDimension`,
  `RingedSite.localization`,
  `RingedSite.Hom.localizedRestrictionDerived`,
  `RingedSite.Hom.ModuleCat`,
  `RingedSite.Hom.ModuleDerived`;
- best owner abstraction: `RingedSite.Hom.ModuleDerived.LocallyHasFiniteTorDimension` is the
  source-facing derived-object owner built from the core predicate `HasFiniteTorDimension` after
  passing to the localized ringed sites `X.localization U`;
- primitive data: an object `E : ModuleDerived X`, an object `U : X`, a covering of `U`, and the
  localized restrictions of `E` to the cover members;
- derived API: the local finite-tor-dimension owner below, with the defining quantifier surface
  exposed directly by the owner itself.

Source/core/bridge triage:
- `source-facing`: the local finite-tor-dimension predicate;
- `core/canonical`: `HasFiniteTorDimension`, `RingedSite.localization`, and
  `RingedSite.Hom.localizedRestrictionDerived`;
- `bridge/view`: a site presentation `X = RingedSite.ofCommRingSheaf J 𝒪`, which specializes this
  ambient-owner formulation rather than owning a parallel local-finite-tor-dimension API. -/

/-- Definition 21.46.1 (3): an object `E` of `ModuleDerived X` locally has finite Tor dimension
if for every object `U : X` there is a covering of `U` on whose members the restriction of `E`
has finite Tor dimension. -/
@[stacks 08FZ]
def LocallyHasFiniteTorDimension (E : DMod) : Prop :=
  ∀ U : X, ∃ T : X.siteTopology.Cover U, ∀ I : T.Arrow,
    HasFiniteTorDimension ((localizedRestrictionDerived X I.Y).obj E)

end

end ModuleDerived
end Hom
end RingedSite

section

variable {X : RingedSite.{u, v}}

variable [HasBinaryProducts X.carrier]
variable [∀ U : X, MonoidalCategory (RingedSite.Hom.ModuleDerived (X.localization U))]
variable [∀ U : X, (RingedSite.Hom.localizedRestriction X U).Additive]
variable [∀ U : X, PreservesFiniteLimits (RingedSite.Hom.localizedRestriction X U)]
variable [∀ U : X, PreservesFiniteColimits (RingedSite.Hom.localizedRestriction X U)]

namespace RingedSite.Hom.ModuleDerived

open SheafOfModules.RingedSite

/-- A locally finite-Tor-dimension object admits, over every `U : X`, a covering on whose members
its localized restrictions have finite Tor dimension. -/
theorem LocallyHasFiniteTorDimension.exists_cover
    {E : ModuleDerived X} (hE : LocallyHasFiniteTorDimension E) (U : X) :
    ∃ T : X.siteTopology.Cover U, ∀ I : T.Arrow,
      HasFiniteTorDimension ((localizedRestrictionDerived X I.Y).obj E) :=
  hE U

end RingedSite.Hom.ModuleDerived

end
