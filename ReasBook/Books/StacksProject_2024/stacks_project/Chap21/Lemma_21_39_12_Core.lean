import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import StacksProject_2024.Chap18.Lemma_18_14_2
import StacksProject_2024.Chap18.RingedSiteModuleCategory
import StacksProject_2024.Chap21.Lemma_21_39_7

open CategoryTheory Opposite SheafOfModules.RingedSite
open CategoryTheory.Limits

noncomputable section

attribute [local instance] HasDerivedCategory.standard

universe u

namespace CategoryTheory.ModulesOnCategory

variable {C : Type u} [Category.{u} C]
variable [((⊥ : GrothendieckTopology C)).HasSheafCompose (forget₂ CommRingCat RingCat.{u})]

local notation "J" => (⊥ : GrothendieckTopology C)

private abbrev AbPresheaf
    (C : Type u) [Category.{u} C] :=
  Cᵒᵖ ⥤ AddCommGrpCat.{u}

local notation "QisAbPresheaf" =>
  HomotopyCategory.quasiIso (AbPresheaf C) (ComplexShape.up ℤ)

local instance instPreadditiveModuleSheaf
    (𝒪 : Sheaf J CommRingCat.{u})
    [Abelian (ringedSiteModuleCategory J 𝒪)] :
    Preadditive (ringedSiteModuleCategory J 𝒪) :=
  (inferInstance : Abelian (ringedSiteModuleCategory J 𝒪)).toPreadditive

local instance instPreadditiveAbPresheaf : Preadditive (AbPresheaf C) :=
  (inferInstance : Abelian (AbPresheaf C)).toPreadditive

/-- The underlying abelian presheaf functor on module sheaves over the chaotic topology. -/
abbrev underlyingAbelianPresheafFunctor
    (𝒪 : Sheaf J CommRingCat.{u}) :
    ringedSiteModuleCategory J 𝒪 ⥤ AbPresheaf C :=
  SheafOfModules.toSheaf (ringSheaf J 𝒪) ⋙
    sheafToPresheaf J AddCommGrpCat.{u}

private theorem underlyingAbelianPresheafFunctor_exact
    (𝒪 : Sheaf J CommRingCat.{u}) :
    exactFunctor
      (ringedSiteModuleCategory J 𝒪)
      (AbPresheaf C)
      (underlyingAbelianPresheafFunctor 𝒪) := by
  sorry

/-- The canonical derived forgetful functor from `D(\mathcal O)` to derived abelian presheaves on
the chaotic site. -/
noncomputable abbrev underlyingAbelianPresheafDerived
    (𝒪 : Sheaf J CommRingCat.{u})
    [Abelian (ringedSiteModuleCategory J 𝒪)] :
    DerivedCategory (ringedSiteModuleCategory J 𝒪) ⥤ DerivedCategory (AbPresheaf C) :=
  let F := underlyingAbelianPresheafFunctor 𝒪
  letI : Preadditive (ringedSiteModuleCategory J 𝒪) :=
    (inferInstance : Abelian (ringedSiteModuleCategory J 𝒪)).toPreadditive
  letI : Preadditive (AbPresheaf C) :=
    (inferInstance : Abelian (AbPresheaf C)).toPreadditive
  let hAdd : Functor.Additive F := by
    sorry
  let hLim : PreservesFiniteLimits F := by
    simpa [F] using (exactFunctor_iff F).mp (underlyingAbelianPresheafFunctor_exact 𝒪) |>.1
  let hColim : PreservesFiniteColimits F := by
    simpa [F] using (exactFunctor_iff F).mp (underlyingAbelianPresheafFunctor_exact 𝒪) |>.2
  @Functor.mapDerivedCategory _ _ _ _ _ _ _ _ F hAdd hLim hColim

/-- The canonical abelian-valued derived lower shriek `L\pi_!` for `\mathcal O`-modules on a
category with the chaotic topology. -/
noncomputable abbrev derivedLowerShriekToPoint
    (𝒪 : Sheaf J CommRingCat.{u})
    [Abelian (ringedSiteModuleCategory J 𝒪)]
    [HasColimitsOfShape Cᵒᵖ AddCommGrpCat.{u}]
    [Functor.HasLeftDerivedFunctor
      (categoryOverPointColimitToDerived C AddCommGrpCat.{u} :
        HomotopyCategory (AbPresheaf C) (ComplexShape.up ℤ) ⥤
          DerivedCategory AddCommGrpCat.{u})
      QisAbPresheaf] :
    DerivedCategory (ringedSiteModuleCategory J 𝒪) ⥤
      DerivedCategory AddCommGrpCat.{u} :=
  underlyingAbelianPresheafDerived 𝒪 ⋙
    (categoryOverPointDerivedColimit C AddCommGrpCat.{u} :
      DerivedCategory (AbPresheaf C) ⥤ DerivedCategory AddCommGrpCat.{u})

end CategoryTheory.ModulesOnCategory
