import Mathlib
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import StacksProject_2024.Chap18.Lemma_18_27_9
import StacksProject_2024.Chap21.Definition_21_17_13

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open SheafOfModules.RingedSite

noncomputable section

universe u

attribute [local instance] HasDerivedCategory.standard

set_option checkBinderAnnotations false

section

variable {C : Type u} [Category.{u} C]
variable (J : GrothendieckTopology C)
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [HasWeakSheafify J AddCommGrpCat.{u}]
variable [HasSheafify J AddCommGrpCat.{u}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable (𝒪 : Sheaf J CommRingCat.{u}) (U : C)

private abbrev localizedStructureMap :=
  (((sheafCompose J (forget₂ CommRingCat RingCat)).obj 𝒪).over U)

/-- The ambient category of `\mathcal O`-modules on the fixed ringed site. -/
private abbrev ambientModuleCategory :=
  SheafOfModules ((sheafCompose J (forget₂ CommRingCat RingCat)).obj 𝒪)

/-- The category of `\mathcal O_U`-modules on the localized ringed site over `U`. -/
private abbrev localizedModuleCategory :=
  SheafOfModules ((sheafCompose (J.over U) (forget₂ CommRingCat RingCat)).obj (𝒪.over U))

/-- The ambient derived category `D(\mathcal O)`. -/
private abbrev ambientDerivedCategory :=
  DerivedCategory (ambientModuleCategory J 𝒪)

/-- The localized derived category `D(\mathcal O_U)`. -/
private abbrev localizedDerivedCategory :=
  DerivedCategory (localizedModuleCategory J 𝒪 U)

/-- Restriction from the ambient ringed site to the localization at `U`. -/
private abbrev localizedRestriction :
    ambientModuleCategory J 𝒪 ⥤ localizedModuleCategory J 𝒪 U :=
  SheafOfModules.pushforward (𝟙 (localizedStructureMap J 𝒪 U))

/-- Extension by zero from the localization at `U` back to the ambient ringed site. -/
private abbrev localizedExtensionByZero :
    localizedModuleCategory J 𝒪 U ⥤ ambientModuleCategory J 𝒪 :=
  SheafOfModules.pullback (𝟙 (localizedStructureMap J 𝒪 U))

variable [CategoryWithHomology (ambientModuleCategory J 𝒪)]
variable [HasCountableCoproducts (ambientModuleCategory J 𝒪)]
variable [MonoidalCategory (ambientModuleCategory J 𝒪)]
variable [MonoidalPreadditive (ambientModuleCategory J 𝒪)]
variable [HasColimits (ambientModuleCategory J 𝒪)]
variable [(curriedTensor (ambientModuleCategory J 𝒪)).Additive]
variable [∀ X : ambientModuleCategory J 𝒪,
  ((curriedTensor (ambientModuleCategory J 𝒪)).obj X).Additive]
variable [∀ (X Y : CochainComplex (ambientModuleCategory J 𝒪) ℤ),
  CochainComplex.HasMapBifunctor X Y (curriedTensor (ambientModuleCategory J 𝒪))]

variable [CategoryWithHomology (localizedModuleCategory J 𝒪 U)]
variable [HasCountableCoproducts (localizedModuleCategory J 𝒪 U)]
variable [MonoidalCategory (localizedModuleCategory J 𝒪 U)]
variable [MonoidalPreadditive (localizedModuleCategory J 𝒪 U)]
variable [HasColimits (localizedModuleCategory J 𝒪 U)]
variable [(curriedTensor (localizedModuleCategory J 𝒪 U)).Additive]
variable [∀ X : localizedModuleCategory J 𝒪 U,
  ((curriedTensor (localizedModuleCategory J 𝒪 U)).obj X).Additive]
variable [∀ (X Y : CochainComplex (localizedModuleCategory J 𝒪 U) ℤ),
  CochainComplex.HasMapBifunctor X Y (curriedTensor (localizedModuleCategory J 𝒪 U))]

/-- The localized category has the chosen homological structure. -/
local instance instCategoryWithHomologyLocalizedModuleCategory :
    CategoryWithHomology (localizedModuleCategory J 𝒪 U) :=
  inferInstanceAs (CategoryWithHomology (localizedModuleCategory J 𝒪 U))

/-- The localized category has countable coproducts. -/
local instance instHasCountableCoproductsLocalizedModuleCategory :
    HasCountableCoproducts (localizedModuleCategory J 𝒪 U) :=
  inferInstanceAs (HasCountableCoproducts (localizedModuleCategory J 𝒪 U))

/-- The localized category carries the chosen monoidal structure. -/
local instance instMonoidalCategoryLocalizedModuleCategory :
    MonoidalCategory (localizedModuleCategory J 𝒪 U) :=
  inferInstanceAs (MonoidalCategory (localizedModuleCategory J 𝒪 U))

/-- The localized category is monoidal preadditive. -/
local instance instMonoidalPreadditiveLocalizedModuleCategory :
    MonoidalPreadditive (localizedModuleCategory J 𝒪 U) :=
  inferInstanceAs (MonoidalPreadditive (localizedModuleCategory J 𝒪 U))

/-- The localized category has all colimits. -/
local instance instHasColimitsLocalizedModuleCategory :
    HasColimits (localizedModuleCategory J 𝒪 U) :=
  inferInstanceAs (HasColimits (localizedModuleCategory J 𝒪 U))

/-- The curried tensor functor on the localized category is additive. -/
local instance instCurriedTensorAdditiveLocalizedModuleCategory :
    (curriedTensor (localizedModuleCategory J 𝒪 U)).Additive :=
  inferInstanceAs ((curriedTensor (localizedModuleCategory J 𝒪 U)).Additive)

/-- Tensoring on the localized category is additive in the variable object. -/
local instance instTensorObjAdditiveLocalizedModuleCategory :
    ∀ X : localizedModuleCategory J 𝒪 U,
      ((curriedTensor (localizedModuleCategory J 𝒪 U)).obj X).Additive :=
  inferInstanceAs
    (∀ X : localizedModuleCategory J 𝒪 U,
      ((curriedTensor (localizedModuleCategory J 𝒪 U)).obj X).Additive)

/-- The localized tensor product admits the standard map bifunctor on cochain complexes. -/
local instance instHasMapBifunctorLocalizedModuleCategory :
    ∀ (X Y : CochainComplex (localizedModuleCategory J 𝒪 U) ℤ),
      CochainComplex.HasMapBifunctor X Y (curriedTensor (localizedModuleCategory J 𝒪 U)) :=
  inferInstanceAs
    (∀ (X Y : CochainComplex (localizedModuleCategory J 𝒪 U) ℤ),
      CochainComplex.HasMapBifunctor X Y (curriedTensor (localizedModuleCategory J 𝒪 U)))

/-- Extension by zero preserves finite limits on module sheaves. -/
local instance instPreservesFiniteLimitsJShriek :
    PreservesFiniteLimits (localizedExtensionByZero J 𝒪 U) := sorry

/-- Extension by zero preserves finite colimits on module sheaves. -/
local instance instPreservesFiniteColimitsJShriek :
    PreservesFiniteColimits (localizedExtensionByZero J 𝒪 U) := sorry

/-- Extension by zero is additive on module sheaves. -/
local instance instAdditiveJShriek :
    (localizedExtensionByZero J 𝒪 U).Additive := sorry

/-- Restriction to the localized ringed site preserves finite limits on module sheaves. -/
local instance instPreservesFiniteLimitsJStar :
    PreservesFiniteLimits (localizedRestriction J 𝒪 U) := sorry

/-- Restriction to the localized ringed site preserves finite colimits on module sheaves. -/
local instance instPreservesFiniteColimitsJStar :
    PreservesFiniteColimits (localizedRestriction J 𝒪 U) := sorry

/-- Restriction to the localized ringed site is additive on module sheaves. -/
local instance instAdditiveJStar :
    (localizedRestriction J 𝒪 U).Additive := sorry

/-- The derived tensor product endofunctor on `D(\mathcal O)` specialized to the current ringed
site. -/
private abbrev ambientDerivedTensorProduct :
    ambientDerivedCategory J 𝒪 →
      ambientDerivedCategory J 𝒪 ⥤ ambientDerivedCategory J 𝒪 :=
  show ambientDerivedCategory J 𝒪 →
      ambientDerivedCategory J 𝒪 ⥤ ambientDerivedCategory J 𝒪 from
    derivedTensorProduct

/-- The derived tensor product endofunctor on `D(\mathcal O_U)` specialized to the localized
ringed site over `U`. -/
private abbrev localizedDerivedTensorProduct :
    localizedDerivedCategory J 𝒪 U →
      localizedDerivedCategory J 𝒪 U ⥤ localizedDerivedCategory J 𝒪 U :=
  show localizedDerivedCategory J 𝒪 U →
      localizedDerivedCategory J 𝒪 U ⥤ localizedDerivedCategory J 𝒪 U from
    derivedTensorProduct

/-- The functor on derived categories induced by extension by zero. -/
private abbrev derivedLocalizedExtensionByZero :
    localizedDerivedCategory J 𝒪 U ⥤ ambientDerivedCategory J 𝒪 :=
  show localizedDerivedCategory J 𝒪 U ⥤ ambientDerivedCategory J 𝒪 from
    Functor.mapDerivedCategory (localizedExtensionByZero J 𝒪 U)

/-- The functor on derived categories induced by localization restriction. -/
private abbrev derivedLocalizedRestriction :
    ambientDerivedCategory J 𝒪 ⥤ localizedDerivedCategory J 𝒪 U :=
  show ambientDerivedCategory J 𝒪 ⥤ localizedDerivedCategory J 𝒪 U from
    Functor.mapDerivedCategory (localizedRestriction J 𝒪 U)

-- Proof sketch: represent `L` by a complex of `\mathcal O_U`-modules and `K` by a K-flat
-- complex of `\mathcal O`-modules. Apply the underived comparison isomorphism of
-- Lemma `18.27.9` degreewise to identify tensoring after `j_{U!}` with `j_{U!}` after
-- restriction and tensoring, then pass to the derived category through the chosen K-flat model
-- of `K`.
/-- Lemma 21.20.9: for a ringed site `(\mathcal C, \mathcal O)`, an object `U : \mathcal C`,
an object `L` of `D(\mathcal O_U)`, and an object `K` of `D(\mathcal O)`, derived tensoring with
`K` commutes with extension by zero from the localized ringed site:
`j_{U!}L \otimes_{\mathcal O}^{\mathbf L} K \cong
j_{U!}(L \otimes_{\mathcal O_U}^{\mathbf L} K|_U)`. -/
theorem ringedSiteLocalizedExtensionByZero_derivedTensorProduct_isIsomorphic
    (L : localizedDerivedCategory J 𝒪 U) (K : ambientDerivedCategory J 𝒪) :
    IsIsomorphic
      (((ambientDerivedTensorProduct J 𝒪 K).obj ((derivedLocalizedExtensionByZero J 𝒪 U).obj L)))
      (((derivedLocalizedExtensionByZero J 𝒪 U).obj
        ((localizedDerivedTensorProduct J 𝒪 U ((derivedLocalizedRestriction J 𝒪 U).obj K)).obj
          L))) := sorry

end
