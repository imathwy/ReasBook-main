import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import StacksProject_2024.Chap18.RingedSiteModuleCategory
import StacksProject_2024.Chap21.Lemma_21_18_2
import StacksProject_2024.Chap21.Lemma_21_39_7

open CategoryTheory
open CategoryTheory.Limits
open ComplexShape
open Opposite
open SheafOfModules.RingedSite

noncomputable section

attribute [local instance] HasDerivedCategory.standard

universe u

namespace CategoryTheory.ModulesOnCategory

private abbrev ConstB
    (C : Type u) [Category.{u} C]
    (B : Type u) [CommRing B] :
    Sheaf (⊥ : GrothendieckTopology C) CommRingCat.{u} :=
  (constantSheaf (⊥ : GrothendieckTopology C) CommRingCat.{u}).obj (CommRingCat.of B)

private abbrev BPresheaf
    (C : Type u) [Category.{u} C]
    (B : Type u) [CommRing B] :=
  Cᵒᵖ ⥤ ModuleCat B

private abbrev AbPresheaf
    (C : Type u) [Category.{u} C] :=
  Cᵒᵖ ⥤ AddCommGrpCat.{u}

/-- The underlying abelian presheaf functor on module sheaves over the chaotic topology. -/
abbrev underlyingAbelianPresheafFunctor
    {C : Type u} [Category.{u} C]
    [((⊥ : GrothendieckTopology C)).HasSheafCompose (forget₂ CommRingCat RingCat.{u})]
    (𝒪 : Sheaf (⊥ : GrothendieckTopology C) CommRingCat.{u}) :
    ringedSiteModuleCategory (⊥ : GrothendieckTopology C) 𝒪 ⥤ AbPresheaf C :=
  SheafOfModules.toSheaf (ringSheaf (⊥ : GrothendieckTopology C) 𝒪) ⋙
    sheafToPresheaf (⊥ : GrothendieckTopology C) AddCommGrpCat.{u}

private theorem underlyingAbelianPresheafFunctor_exact
    {C : Type u} [Category.{u} C]
    [((⊥ : GrothendieckTopology C)).HasSheafCompose (forget₂ CommRingCat RingCat.{u})]
    (𝒪 : Sheaf (⊥ : GrothendieckTopology C) CommRingCat.{u}) :
    exactFunctor
      (ringedSiteModuleCategory (⊥ : GrothendieckTopology C) 𝒪)
      (AbPresheaf C)
      (underlyingAbelianPresheafFunctor 𝒪) := by
  sorry

local instance underlyingAbelianPresheafFunctor_additive
    {C : Type u} [Category.{u} C]
    [((⊥ : GrothendieckTopology C)).HasSheafCompose (forget₂ CommRingCat RingCat.{u})]
    (𝒪 : Sheaf (⊥ : GrothendieckTopology C) CommRingCat.{u}) :
    Functor.Additive (underlyingAbelianPresheafFunctor 𝒪) := by
  change
    Functor.Additive
      (SheafOfModules.toSheaf (ringSheaf (⊥ : GrothendieckTopology C) 𝒪) ⋙
        sheafToPresheaf (⊥ : GrothendieckTopology C) AddCommGrpCat.{u})
  infer_instance

/-- The canonical derived forgetful functor from `D(\mathcal O)` to derived abelian presheaves on
the chaotic site. -/
noncomputable abbrev underlyingAbelianPresheafDerived
    {C : Type u} [Category.{u} C]
    [((⊥ : GrothendieckTopology C)).HasSheafCompose (forget₂ CommRingCat RingCat.{u})]
    (𝒪 : Sheaf (⊥ : GrothendieckTopology C) CommRingCat.{u})
    [Abelian (ringedSiteModuleCategory (⊥ : GrothendieckTopology C) 𝒪)] :
    DerivedCategory (ringedSiteModuleCategory (⊥ : GrothendieckTopology C) 𝒪) ⥤
      DerivedCategory (AbPresheaf C) :=
  let F := underlyingAbelianPresheafFunctor 𝒪
  letI : F.Additive := by
    change
      Functor.Additive
        (SheafOfModules.toSheaf (ringSheaf (⊥ : GrothendieckTopology C) 𝒪) ⋙
          sheafToPresheaf (⊥ : GrothendieckTopology C) AddCommGrpCat.{u})
    infer_instance
  letI : PreservesFiniteLimits F := by
    simpa [F] using (exactFunctor_iff F).mp (underlyingAbelianPresheafFunctor_exact 𝒪) |>.1
  letI : PreservesFiniteColimits F := by
    simpa [F] using (exactFunctor_iff F).mp (underlyingAbelianPresheafFunctor_exact 𝒪) |>.2
  F.mapDerivedCategory

/-- The canonical abelian-valued derived lower shriek `L\pi_!` for `\mathcal O`-modules on a
category with the chaotic topology. -/
noncomputable abbrev derivedLowerShriekToPoint
    {C : Type u} [Category.{u} C]
    [((⊥ : GrothendieckTopology C)).HasSheafCompose (forget₂ CommRingCat RingCat.{u})]
    (𝒪 : Sheaf (⊥ : GrothendieckTopology C) CommRingCat.{u})
    [Abelian (ringedSiteModuleCategory (⊥ : GrothendieckTopology C) 𝒪)]
    [HasColimitsOfShape Cᵒᵖ AddCommGrpCat.{u}]
    [Functor.HasLeftDerivedFunctor
      (categoryOverPointColimitToDerived C AddCommGrpCat.{u} :
        HomotopyCategory (AbPresheaf C) (up ℤ) ⥤ DerivedCategory AddCommGrpCat.{u})
      (HomotopyCategory.quasiIso (AbPresheaf C) (up ℤ))] :
    DerivedCategory (ringedSiteModuleCategory (⊥ : GrothendieckTopology C) 𝒪) ⥤
      DerivedCategory AddCommGrpCat.{u} :=
  underlyingAbelianPresheafDerived 𝒪 ⋙
    (categoryOverPointDerivedColimit C AddCommGrpCat.{u} :
      DerivedCategory (AbPresheaf C) ⥤ DerivedCategory AddCommGrpCat.{u})

private abbrev constantRingPresheaf
    (C : Type u) [Category.{u} C]
    (B : Type u) [CommRing B] :
    Cᵒᵖ ⥤ RingCat.{u} :=
  (Functor.const Cᵒᵖ).obj (RingCat.of B)

private abbrev constantRingSheafIso
    (C : Type u) [Category.{u} C]
    (B : Type u) [CommRing B]
    [((⊥ : GrothendieckTopology C)).HasSheafCompose (forget₂ CommRingCat RingCat.{u})]
    [((⊥ : GrothendieckTopology C)).PreservesSheafification (forget₂ CommRingCat RingCat.{u})] :
    ringSheaf (⊥ : GrothendieckTopology C) (ConstB C B) ≅
      (constantSheaf (⊥ : GrothendieckTopology C) RingCat.{u}).obj (RingCat.of B) :=
  (constantCommuteCompose
      (⊥ : GrothendieckTopology C)
      (forget₂ CommRingCat RingCat.{u})).app (CommRingCat.of B)

private noncomputable abbrev constantRingPresheafToRingSheaf
    (C : Type u) [Category.{u} C]
    (B : Type u) [CommRing B]
    [HasWeakSheafify (⊥ : GrothendieckTopology C) RingCat.{u}]
    [((⊥ : GrothendieckTopology C)).HasSheafCompose (forget₂ CommRingCat RingCat.{u})]
    [((⊥ : GrothendieckTopology C)).PreservesSheafification (forget₂ CommRingCat RingCat.{u})] :
    constantRingPresheaf C B ⟶
      (ringSheaf (⊥ : GrothendieckTopology C) (ConstB C B)).obj :=
  (show
      constantRingPresheaf C B ⟶
        ((constantSheaf (⊥ : GrothendieckTopology C) RingCat.{u}).obj (RingCat.of B)).obj
    by
      simpa [constantRingPresheaf, constantSheaf] using
        (toSheafify (⊥ : GrothendieckTopology C) (constantRingPresheaf C B))) ≫
    (constantRingSheafIso C B).inv.hom

private abbrev constantSheafModuleToConstantPresheafModule
    (C : Type u) [Category.{u} C]
    (B : Type u) [CommRing B]
    [HasWeakSheafify (⊥ : GrothendieckTopology C) RingCat.{u}]
    [((⊥ : GrothendieckTopology C)).HasSheafCompose (forget₂ CommRingCat RingCat.{u})]
    [((⊥ : GrothendieckTopology C)).PreservesSheafification (forget₂ CommRingCat RingCat.{u})] :
    ringedSiteModuleCategory (⊥ : GrothendieckTopology C) (ConstB C B) ⥤
      PresheafOfModules (constantRingPresheaf C B) :=
  SheafOfModules.forget (ringSheaf (⊥ : GrothendieckTopology C) (ConstB C B)) ⋙
    PresheafOfModules.restrictScalars (constantRingPresheafToRingSheaf C B)

private theorem constantPresheafToBPresheaf_exact
    (C : Type u) [Category.{u} C]
    (B : Type u) [CommRing B] :
    exactFunctor
      (PresheafOfModules (constantRingPresheaf C B))
      (BPresheaf C B)
      (PresheafOfModules.toPresheaf (constantRingPresheaf C B)) := by
  simpa [BPresheaf] using
    (ExactFunctor.of (PresheafOfModules.toPresheaf (constantRingPresheaf C B))).property

private theorem constantSheafModuleToBPresheaf_exact
    (C : Type u) [Category.{u} C]
    (B : Type u) [CommRing B]
    [HasWeakSheafify (⊥ : GrothendieckTopology C) RingCat.{u}]
    [((⊥ : GrothendieckTopology C)).HasSheafCompose (forget₂ CommRingCat RingCat.{u})]
    [((⊥ : GrothendieckTopology C)).PreservesSheafification (forget₂ CommRingCat RingCat.{u})] :
    exactFunctor
      (ringedSiteModuleCategory (⊥ : GrothendieckTopology C) (ConstB C B))
      (BPresheaf C B)
      (constantSheafModuleToConstantPresheafModule C B ⋙
        PresheafOfModules.toPresheaf (constantRingPresheaf C B)) := by
  sorry

noncomputable abbrev constantSheafModuleDerivedToBPresheaf
    (C : Type u) [Category.{u} C]
    (B : Type u) [CommRing B]
    [HasWeakSheafify (⊥ : GrothendieckTopology C) RingCat.{u}]
    [((⊥ : GrothendieckTopology C)).HasSheafCompose (forget₂ CommRingCat RingCat.{u})]
    [((⊥ : GrothendieckTopology C)).PreservesSheafification (forget₂ CommRingCat RingCat.{u})]
    [Abelian (ringedSiteModuleCategory (⊥ : GrothendieckTopology C) (ConstB C B))] :
      DerivedCategory (ringedSiteModuleCategory (⊥ : GrothendieckTopology C) (ConstB C B)) ⥤
      DerivedCategory (BPresheaf C B) :=
  let F :=
    constantSheafModuleToConstantPresheafModule C B ⋙
      PresheafOfModules.toPresheaf (constantRingPresheaf C B)
  letI : F.Additive := by
    infer_instance
  letI : PreservesFiniteLimits F := by
    simpa [F] using (exactFunctor_iff F).mp (constantSheafModuleToBPresheaf_exact C B) |>.1
  letI : PreservesFiniteColimits F := by
    simpa [F] using (exactFunctor_iff F).mp (constantSheafModuleToBPresheaf_exact C B) |>.2
  F.mapDerivedCategory

/- Domain-style sampling for Remark 21.39.13:
- primary domain: same-site change of structure sheaf to the constant sheaf `\underline B`,
  followed by the derived lower shriek `L\pi_!` for the projection from a category with the
  chaotic topology to a point;
- sampled owner declarations:
  `derivedLowerShriekToPoint`,
  `leftDerivedPullback`,
  `ringedSiteStructureMap`,
  `SheafOfModules.unitToPushforwardObjUnit`,
  `categoryOverPointDerivedColimit`;
- best owner abstraction: the public owner is the canonical `D(\mathcal O) ⥤ D(B)` composite
  built from same-site derived pullback to `\underline B` and the point-lower-shriek owner on
  `B`-module presheaves;
- primitive data: the structure map `β : \mathcal O ⟶ \underline B`;
- derived API: the exact functor below and the companion factorization theorem. -/

/-- The canonical `D(B)`-valued exact functor of Remark `21.39.13`: tensor an object of
`D(\mathcal O)` with the constant sheaf `\underline B` via same-site derived pullback, then
apply the Chapter 21 lower shriek owner `L\pi_! : D(B^{--}) \to D(B)`. -/
noncomputable abbrev derivedLowerShriekThroughBModules
    {C : Type u} [Category.{u} C]
    {B : Type u} [CommRing B]
    [HasWeakSheafify (⊥ : GrothendieckTopology C) RingCat.{u}]
    [((⊥ : GrothendieckTopology C)).HasSheafCompose (forget₂ CommRingCat RingCat.{u})]
    [((⊥ : GrothendieckTopology C)).PreservesSheafification (forget₂ CommRingCat RingCat.{u})]
    (𝒪 : Sheaf (⊥ : GrothendieckTopology C) CommRingCat.{u})
    [HasSheafify (⊥ : GrothendieckTopology C) AddCommGrpCat.{u}]
    [((⊥ : GrothendieckTopology C)).WEqualsLocallyBijective AddCommGrpCat.{u}]
    {β : 𝒪 ⟶ ConstB C B}
    [Abelian (ringedSiteModuleCategory (⊥ : GrothendieckTopology C) 𝒪)]
    [Abelian (ringedSiteModuleCategory (⊥ : GrothendieckTopology C) (ConstB C B))]
    [CategoryWithHomology (ringedSiteModuleCategory (⊥ : GrothendieckTopology C) 𝒪)]
    [CategoryWithHomology (ringedSiteModuleCategory (⊥ : GrothendieckTopology C) (ConstB C B))]
    [MonoidalCategory (ringedSiteModuleCategory (⊥ : GrothendieckTopology C) 𝒪)]
    [MonoidalPreadditive (ringedSiteModuleCategory (⊥ : GrothendieckTopology C) 𝒪)]
    [MonoidalCategory (ringedSiteModuleCategory (⊥ : GrothendieckTopology C) (ConstB C B))]
    [MonoidalPreadditive
      (ringedSiteModuleCategory (⊥ : GrothendieckTopology C) (ConstB C B))]
    [(SheafOfModules.pushforward (ringedSiteUnderlyingStructureMap (F := 𝟭 C) β)).IsRightAdjoint]
    [Functor.Additive (pullbackFunctor (F := 𝟭 C) β)]
    [HasColimitsOfShape Cᵒᵖ (ModuleCat B)]
    [Functor.HasLeftDerivedFunctor
      (categoryOverPointColimitToDerived C (ModuleCat B) :
        HomotopyCategory (BPresheaf C B) (up ℤ) ⥤ DerivedCategory (ModuleCat B))
      (HomotopyCategory.quasiIso (BPresheaf C B) (up ℤ))] :

end CategoryTheory.ModulesOnCategory
