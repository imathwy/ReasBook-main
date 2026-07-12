import StacksProject_2024.Chap18.RingedSiteModuleCategory
import StacksProject_2024.Chap21.Lemma_21_18_2
import StacksProject_2024.Chap21.Lemma_21_39_12_Core

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Opposite SheafOfModules.RingedSite RingedSite.Hom
open CategoryTheory.Limits
open scoped Simplicial

noncomputable section

attribute [local instance] HasDerivedCategory.standard

universe u

namespace CategoryTheory.ModulesOnCategory

variable {C : Type u} [Category.{u} C]
variable [((⊥ : GrothendieckTopology C)).HasSheafCompose (forget₂ CommRingCat RingCat.{u})]

local notation "J" => (⊥ : GrothendieckTopology C)

/- Domain-style sampling for Lemma 21.39.12:
- primary domain: change of structure sheaf for module sheaves on a category with the chaotic
  topology, together with the derived lower shriek to a point;
- sampled owner declarations:
  `SheafOfModules.RingedSite.ringedSiteModuleCategory`,
  `SheafOfModules.RingedSite.ringedSiteStructureMap`,
  `SheafOfModules.unitToPushforwardObjUnit`,
  `RingedSite.Hom.modulePullbackDerived`,
  `CategoryTheory.categoryOverPointDerivedColimit`;
  same-site change-of-rings bridge `ringedSiteStructureMap α`, the Chapter 21 derived pullback
  owner `RingedSite.Hom.modulePullbackDerived (sameSiteHom α)`, and the chapter-level
  point-lower-shriek owner `derivedLowerShriekToPoint`, built from
  `categoryOverPointDerivedColimit` and the canonical forgetful composite
  `SheafOfModules.toSheaf (ringSheaf J 𝒪) ⋙ sheafToPresheaf J AddCommGrpCat`;
- primitive data: the structure-sheaf morphism `α : 𝒪 ⟶ 𝒪'`, the canonical unit-module map
  `unitToPushforwardObjUnit (ringedSiteStructureMap α)`, and the canonical forgetful functor from
  module sheaves to abelian presheaves on the chaotic site;
- derived API: the lower-shriek comparison theorem below.

Primitive-vs-derived split:
- primitive data: `α`, the unit-module map induced by `α`, and the same-site pullback functor on
  module sheaves;
- derived API: the induced functor on derived categories and the lower-shriek comparison.

Source/core/bridge triage:
- `source-facing`: the change-of-structure-sheaf lemma for the projection to a point;
  and `derivedLowerShriekToPoint`;
- `bridge/view`: the exact forgetful functor from `𝒪`-modules to abelian presheaves on
  the chaotic site. -/

private abbrev AbPresheaf
    (C : Type u) [Category.{u} C] :=
  Cᵒᵖ ⥤ AddCommGrpCat.{u}

local notation "QisAbPresheaf" =>
  HomotopyCategory.quasiIso (AbPresheaf C) (ComplexShape.up ℤ)

/-- Lemma 21.39.12: if there exists a cosimplicial object of `C` to which Lemma `21.39.7`
applies and if the induced map on `Lπ! 𝒪` is an isomorphism, then the two canonical
lower-shriek objects are isomorphic after change of structure sheaf.

This file keeps the source-facing comparison at the proposition-level owner `IsIsomorphic`,
rather than choosing a public `Iso` witness from that comparison. -/
@[stacks 08RX]
theorem derivedLowerShriek_isomorphic_after_tensor_structureSheafChange
    (𝒪 : Sheaf J CommRingCat.{u})
    {𝒪' : Sheaf J CommRingCat.{u}}
    (α : 𝒪 ⟶ 𝒪')
    [HasColimitsOfShape Cᵒᵖ AddCommGrpCat.{u}]
    [Functor.HasLeftDerivedFunctor
      (categoryOverPointColimitToDerived C AddCommGrpCat.{u} :
        HomotopyCategory (AbPresheaf C) (ComplexShape.up ℤ) ⥤
          DerivedCategory AddCommGrpCat.{u})
      QisAbPresheaf]
    [(SheafOfModules.pushforward (ringedSiteStructureMap α)).IsRightAdjoint]
    [CategoryWithHomology (ringedSiteModuleCategory J 𝒪)]
    [CategoryWithHomology (ringedSiteModuleCategory J 𝒪')]
    [MonoidalCategory (ringedSiteModuleCategory J 𝒪)]
    [MonoidalPreadditive (ringedSiteModuleCategory J 𝒪)]
    [MonoidalCategory (ringedSiteModuleCategory J 𝒪')]
    [MonoidalPreadditive (ringedSiteModuleCategory J 𝒪')]
    (hUbullet :
      ∃ Ubullet : CosimplicialObject C,
        CosimplicialObjectHasPointlikeHomSpaces Ubullet)
    (hα : IsIso
      ((derivedLowerShriekToPoint 𝒪).map
        ((DerivedCategory.singleFunctor (ringedSiteModuleCategory J 𝒪) (0 : ℤ)).map
          (SheafOfModules.unitToPushforwardObjUnit (ringedSiteStructureMap α)))))
    (K : DerivedCategory (ringedSiteModuleCategory J 𝒪)) :
    IsIsomorphic
      ((derivedLowerShriekToPoint 𝒪).obj K)
      ((derivedLowerShriekToPoint 𝒪').obj
        ((modulePullbackDerived (sameSiteHom α)).obj K)) := by
  -- The remaining work is the source-faithful comparison proof through a cosimplicial generator
  -- resolution for the canonical same-site derived pullback along `sameSiteHom α`.
  sorry

-- The site-local abelian-sheaf hypotheses used to construct
-- `RingedSite.Hom.modulePullbackDerived (sameSiteHom α)` are packaged in the Chapter 21 owner, so
-- they do not need to be repeated explicitly on the theorem surface.

end CategoryTheory.ModulesOnCategory
