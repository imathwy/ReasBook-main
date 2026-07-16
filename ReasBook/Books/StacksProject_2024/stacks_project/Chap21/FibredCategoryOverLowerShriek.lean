import Mathlib.CategoryTheory.Adjunction.Mates
import StacksProject_2024.stacks_project.Chap18.RingedSiteModuleCategory
import StacksProject_2024.stacks_project.Chap21.Lemma_21_20_3
import StacksProject_2024.stacks_project.Chap21.Situation_21_38_3

open CategoryTheory
open CategoryTheory.FibredCategoryMor
open RingedSite.Hom
open scoped RingedSite.Hom

noncomputable section

universe u v

namespace CategoryTheory
namespace FibredCategoryOver

/-- The canonical Grothendieck topology inherited by `C` from the base ringed site `D`. -/
def sourceTopology (D : RingedSite.{u, v}) (C : FibredCategoryOver.{u, v} D) :
    GrothendieckTopology C.S :=
  FibredCategoryOver.inheritedTopology D.siteTopology C

instance comparisonFunctor_isContinuous
    {D : RingedSite.{u, v}} {C C' : FibredCategoryOver.{u, v} D} (u : C' ⟶ C)
    [Functor.IsContinuous C'.p (inheritedTopology D.siteTopology C') D.siteTopology]
    [Functor.IsContinuous C.p (inheritedTopology D.siteTopology C) D.siteTopology]
    [IsMorphismOfSites
      (inheritedTopology D.siteTopology C')
      (inheritedTopology D.siteTopology C)
      (toFunctor u)] :
    Functor.IsContinuous
      (toFunctor u)
      (inheritedTopology D.siteTopology C')
      (inheritedTopology D.siteTopology C) :=
  inferInstance

/-- The module-sheaf inverse-image functor attached to a morphism of fibred categories over a
ringed site. -/
@[stacks 08PC]
def moduleInverseImage
    {D : RingedSite.{u, v}} {C C' : FibredCategoryOver.{u, v} D} (u : C' ⟶ C)
    [Functor.IsContinuous C'.p (inheritedTopology D.siteTopology C') D.siteTopology]
    [Functor.IsContinuous C.p (inheritedTopology D.siteTopology C) D.siteTopology]
    [IsMorphismOfSites
      (inheritedTopology D.siteTopology C')
      (inheritedTopology D.siteTopology C)
      (toFunctor u)] :
    SheafOfModules (inheritedRingedSite D C).structureSheaf ⥤
      SheafOfModules (inheritedRingedSite D C').structureSheaf :=
  RingedSite.Hom.modulePushforward (inheritedRingedSiteHom u)

/-- The underlying abelian-sheaf inverse-image functor attached to a morphism of fibred categories
over a ringed site. -/
@[stacks 08PC]
def abelianInverseImage
    {D : RingedSite.{u, v}} {C C' : FibredCategoryOver.{u, v} D} (u : C' ⟶ C)
    [Functor.IsContinuous C'.p (inheritedTopology D.siteTopology C') D.siteTopology]
    [Functor.IsContinuous C.p (inheritedTopology D.siteTopology C) D.siteTopology]
    [IsMorphismOfSites
      (inheritedTopology D.siteTopology C')
      (inheritedTopology D.siteTopology C)
      (toFunctor u)] :
    Sheaf (sourceTopology D C) AddCommGrpCat.{max u v} ⥤
      Sheaf (sourceTopology D C') AddCommGrpCat.{max u v} :=
  (toFunctor u).sheafPushforwardContinuous
    AddCommGrpCat.{max u v}
    (inheritedTopology D.siteTopology C')
    (inheritedTopology D.siteTopology C)

/-- Forgetting module structure after `moduleInverseImage u` agrees with `abelianInverseImage u`.
-/
theorem moduleInverseImage_comp_underlyingAbelianSheafFunctor
    {D : RingedSite.{u, v}} {C C' : FibredCategoryOver.{u, v} D} (u : C' ⟶ C)
    [Functor.IsContinuous C'.p (inheritedTopology D.siteTopology C') D.siteTopology]
    [Functor.IsContinuous C.p (inheritedTopology D.siteTopology C) D.siteTopology]
    [IsMorphismOfSites
      (inheritedTopology D.siteTopology C')
      (inheritedTopology D.siteTopology C)
      (toFunctor u)] :
    moduleInverseImage u ⋙
        underlyingAbelianSheafFunctor (inheritedRingedSite D C') =
      underlyingAbelianSheafFunctor (inheritedRingedSite D C) ⋙
        abelianInverseImage u :=
  rfl

/-- The module lower-shriek functor, once `moduleInverseImage u` is known to be a right adjoint.
-/
@[stacks 08PC]
def moduleLowerShriek
    {D : RingedSite.{u, v}} {C C' : FibredCategoryOver.{u, v} D} (u : C' ⟶ C)
    [Functor.IsContinuous C'.p (inheritedTopology D.siteTopology C') D.siteTopology]
    [Functor.IsContinuous C.p (inheritedTopology D.siteTopology C) D.siteTopology]
    [IsMorphismOfSites
      (inheritedTopology D.siteTopology C')
      (inheritedTopology D.siteTopology C)
      (toFunctor u)]
    [Functor.IsRightAdjoint (moduleInverseImage u)] :
    SheafOfModules (inheritedRingedSite D C').structureSheaf ⥤
      SheafOfModules (inheritedRingedSite D C).structureSheaf :=
  Functor.leftAdjoint (moduleInverseImage u)

/-- The abelian lower-shriek functor, once `abelianInverseImage u` is known to be a right adjoint.
-/
@[stacks 08PC]
def abelianLowerShriek
    {D : RingedSite.{u, v}} {C C' : FibredCategoryOver.{u, v} D} (u : C' ⟶ C)
    [Functor.IsContinuous C'.p (inheritedTopology D.siteTopology C') D.siteTopology]
    [Functor.IsContinuous C.p (inheritedTopology D.siteTopology C) D.siteTopology]
    [IsMorphismOfSites
      (inheritedTopology D.siteTopology C')
      (inheritedTopology D.siteTopology C)
      (toFunctor u)]
    [Functor.IsRightAdjoint (abelianInverseImage u)] :
    Sheaf (sourceTopology D C') AddCommGrpCat.{max u v} ⥤
      Sheaf (sourceTopology D C) AddCommGrpCat.{max u v} :=
  Functor.leftAdjoint (abelianInverseImage u)

/-- The mate comparison between the abelian and module lower shrieks after forgetting module
structure. -/
@[stacks 08PC]
noncomputable def lowerShriekForgetComparison
    {D : RingedSite.{u, v}} {C C' : FibredCategoryOver.{u, v} D} (u : C' ⟶ C)
    [Functor.IsContinuous C'.p (inheritedTopology D.siteTopology C') D.siteTopology]
    [Functor.IsContinuous C.p (inheritedTopology D.siteTopology C) D.siteTopology]
    [IsMorphismOfSites
      (inheritedTopology D.siteTopology C')
      (inheritedTopology D.siteTopology C)
      (toFunctor u)]
    [Functor.IsRightAdjoint (moduleInverseImage u)]
    [Functor.IsRightAdjoint (abelianInverseImage u)] :
    underlyingAbelianSheafFunctor (inheritedRingedSite D C') ⋙
        abelianLowerShriek u ⟶
      moduleLowerShriek u ⋙
        underlyingAbelianSheafFunctor (inheritedRingedSite D C) :=
  let square :
      TwoSquare
        (moduleInverseImage u)
        (underlyingAbelianSheafFunctor (inheritedRingedSite D C))
        (underlyingAbelianSheafFunctor (inheritedRingedSite D C'))
        (abelianInverseImage u) :=
    TwoSquare.mk
      (moduleInverseImage u)
      (underlyingAbelianSheafFunctor (inheritedRingedSite D C))
      (underlyingAbelianSheafFunctor (inheritedRingedSite D C'))
      (abelianInverseImage u)
      (eqToHom (moduleInverseImage_comp_underlyingAbelianSheafFunctor u))
  ((mateEquiv
        (Adjunction.ofIsRightAdjoint (moduleInverseImage u))
        (Adjunction.ofIsRightAdjoint (abelianInverseImage u))).symm
        square).natTrans

@[stacks 08PC]
instance lowerShriekForgetComparison_isIso
    {D : RingedSite.{u, v}} {C C' : FibredCategoryOver.{u, v} D} (u : C' ⟶ C)
    [Functor.IsContinuous C'.p (inheritedTopology D.siteTopology C') D.siteTopology]
    [Functor.IsContinuous C.p (inheritedTopology D.siteTopology C) D.siteTopology]
    [IsMorphismOfSites
      (inheritedTopology D.siteTopology C')
      (inheritedTopology D.siteTopology C)
      (toFunctor u)]
    [Functor.IsRightAdjoint (moduleInverseImage u)]
    [Functor.IsRightAdjoint (abelianInverseImage u)] :
    IsIso (lowerShriekForgetComparison u) := by
  sorry

end FibredCategoryOver
end CategoryTheory
