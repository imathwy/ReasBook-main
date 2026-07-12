import StacksProject_2024.Chap21.RingedSiteDerivedBasic
import StacksProject_2024.Chap21.Remark_21_35_11

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open CategoryTheory.MonoidalClosed
open Functor.LaxMonoidal
open scoped RingedSiteDerived

noncomputable section

universe u v

attribute [local instance] HasDerivedCategory.standard

namespace RingedSite.Hom

section

/- Domain-style sampling for Lemma 21.35.3:
- primary domain: compatibility of localized restriction on derived categories of module sheaves
  over a ringed site with derived internal Hom;
- sampled owner declarations:
  `RingedSite.Hom.localizedRestrictionDerived`,
  `RingedSite.Hom.ringedSiteLocalizedRestriction_isKInjective`,
  `SheafOfModules.RingedSite.pullbackDerivedInternalHomComparison`,
  `MonoidalClosed.uncurry`;
- best owner abstraction:
  `source-facing`: the canonical localized-restriction/internal-Hom comparison for
    `localizedRestrictionDerived X U`;
  `core/canonical`: the Chapter 21 owner `localizedRestrictionDerived X U`, together with
    K-injective localization from Lemma `21.20.1` and the generic pullback/internal-Hom
    comparison owner of Remark `21.35.11`;
  `bridge/view`: the explicit evaluation-side formula obtained by uncurrying the localized
    comparison morphism.
- primitive data: the ringed site `X`, the localized object `U`, the exact derived restriction
  functor `localizedRestrictionDerived X U`, and its canonical tensor comparison isomorphism;
- derived API: the canonical comparison morphism
  `localizedRestriction_derivedInternalHomComparison` together with its source-facing `IsIso`
  companion instance.

Source/core/bridge triage:
- `source-facing`: the localized-restriction/internal-Hom comparison and its `IsIso` companion
  instance;
- `core/canonical`: `localizedRestrictionDerived`, `ringedSiteLocalizedRestriction_isKInjective`,
  and the generic pullback/internal-Hom comparison formalism;
- `bridge/view`: the evaluation-side formula through `MonoidalClosed.uncurry`.
-/

variable (X : RingedSite.{u, v}) (U : X)

set_option quotPrecheck false in
local notation:20 A " ⟹ " B:19 => (ihom A).obj B

variable [HasBinaryProducts X.carrier]
variable [MonoidalCategory (ModuleDerived X)]
variable [BraidedCategory (ModuleDerived X)]
variable [MonoidalClosed (ModuleDerived X)]
variable [MonoidalCategory (ModuleDerived (X.localization U))]
variable [BraidedCategory (ModuleDerived (X.localization U))]
variable [MonoidalClosed (ModuleDerived (X.localization U))]

variable [PreservesFiniteLimits (localizedRestriction X U)]
variable [PreservesFiniteColimits (localizedRestriction X U)]
variable [Functor.Monoidal (localizedRestrictionDerived X U)]

/-- Lemma 21.35.3: for a ringed site `(C, 𝒪)`, an object `U : C`, and objects `K`, `L` of
`D(𝒪)`, localized restriction carries the derived internal Hom of `K` and `L` to the derived
internal Hom of the localized restrictions via the canonical map
`(K ⟹ L)|_U ⟶ (K|_U ⟹ L|_U)`. This is the specialization of
`SheafOfModules.RingedSite.pullbackDerivedInternalHomComparison` from
Remark `21.35.11` to `j[U]⁻¹`. -/
@[stacks 08JB]
noncomputable def localizedRestriction_derivedInternalHomComparison
    (K L : ModuleDerived X) :
    (localizedRestrictionDerived X U).obj (K ⟹ L) ⟶
      ((localizedRestrictionDerived X U).obj K ⟹ (localizedRestrictionDerived X U).obj L) :=
  SheafOfModules.RingedSite.pullbackDerivedInternalHomComparison
    (localizedRestrictionDerived X U)
    (fun A B ↦ (Functor.Monoidal.μIso (localizedRestrictionDerived X U) A B).symm)
    K
    L

/-- Lemma 21.35.3: for localized restriction to `X.localization U`, the canonical map
`(K ⟹ L)|_U ⟶ (K|_U ⟹ L|_U)` is an isomorphism. The source-facing proof runs by
computing both sides on K-injective representatives and applying Lemma `21.20.1` to keep those
representatives K-injective after restriction. -/
@[stacks 08JB, instance]
instance localizedRestriction_derivedInternalHomComparison_isIso
    (K L : ModuleDerived X) :
    IsIso (localizedRestriction_derivedInternalHomComparison X U K L) := by
  sorry

end

end RingedSite.Hom
