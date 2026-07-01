import Mathlib
import stacks_project.Chap18.Definition_18_19_1
import stacks_project.Chap21.Lemma_21_20_4

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open Opposite

noncomputable section

universe u v

attribute [local instance] HasDerivedCategory.standard

set_option checkBinderAnnotations false

/-- The abelian category `\mathrm{Mod}(\mathcal O_X)` of sheaves of modules on the ringed site
`X`. -/
private abbrev RingedSiteModuleCat (X : RingedSite.{u, v}) :=
  SheafOfModules X.structureSheaf

/-- The abelian category `\mathrm{Mod}(\mathcal O_U)` on the localized ringed site
`X.localization U`. -/
private abbrev LocalizedRingedSiteModuleCat (X : RingedSite.{u, v}) (U : X) :=
  SheafOfModules (X.structureSheaf.over U)

/-- The unbounded derived category `D(\mathcal O_X)` of module sheaves on `X`. -/
private abbrev RingedSiteDerivedCat (X : RingedSite.{u, v}) :=
  DerivedCategory (RingedSiteModuleCat X)

/-- The localized derived category `D(\mathcal O_U)` of module sheaves on `X.localization U`. -/
private abbrev LocalizedRingedSiteDerivedCat (X : RingedSite.{u, v}) (U : X) :=
  DerivedCategory (LocalizedRingedSiteModuleCat X U)

-- Proof sketch: choose the standard derived internal-Hom constructions on `D(\mathcal O_X)` and
-- `D(\mathcal O_U)` by resolving the target with a K-injective complex. Lemma `21.20.1` says
-- restriction preserves K-injective complexes, so applying the same construction after
-- restriction produces the localized derived internal Hom. This yields the comparison
-- isomorphism.
/-- Lemma 21.35.3: for a ringed site `(\mathcal C, \mathcal O)` and an object
`U : \mathcal C`, for objects `K, L` of `D(\mathcal O)` and chosen derived internal-Hom
constructions on the ambient
and localized derived categories, the derived internal Hom of the restrictions `K|_U` and `L|_U`
is canonically isomorphic to the restriction of the derived internal Hom of `K` and `L`. -/
theorem localizedRestriction_derivedInternalHomConstruction_isomorphic
    (X : RingedSite.{u, v}) (U : X)
    [HasDerivedCategory (RingedSiteModuleCat X)]
    [HasDerivedCategory (LocalizedRingedSiteModuleCat X U)]
    [(RingedSite.Hom.localizedRestriction X U).Additive]
    [PreservesFiniteLimits (RingedSite.Hom.localizedRestriction X U)]
    [PreservesFiniteColimits (RingedSite.Hom.localizedRestriction X U)]
    (ambientDerivedInternalHom :
      (RingedSiteDerivedCat X)ᵒᵖ ⥤
        RingedSiteDerivedCat X ⥤
          RingedSiteDerivedCat X)
    (localizedDerivedInternalHom :
      (LocalizedRingedSiteDerivedCat X U)ᵒᵖ ⥤
        LocalizedRingedSiteDerivedCat X U ⥤
          LocalizedRingedSiteDerivedCat X U)
    (K L : RingedSiteDerivedCat X) :
    IsIsomorphic
      ((localizedDerivedInternalHom.obj (op ((RingedSite.Hom.localizedRestrictionDerived X U).obj K))).obj
        ((RingedSite.Hom.localizedRestrictionDerived X U).obj L))
      ((RingedSite.Hom.localizedRestrictionDerived X U).obj
        ((ambientDerivedInternalHom.obj (op K)).obj L)) := sorry
