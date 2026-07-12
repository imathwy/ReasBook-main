import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import StacksProject_2024.Chap18.Definition_18_13_1
import StacksProject_2024.Chap21.Lemma_21_19_1_core
import StacksProject_2024.Chap21.Lemma_21_18_2
import StacksProject_2024.Chap21.Lemma_21_39_12_Core

open CategoryTheory
open CategoryTheory.Limits
open ComplexShape
open Opposite
open RingedSite.Hom
open SheafOfModules.RingedSite
open scoped CategoryTheory RingedSite.Hom RingedSiteDerived

noncomputable section

attribute [local instance] HasDerivedCategory.standard

universe u

namespace CategoryTheory.ModulesOnCategory

section

variable {C : Type u} [Category.{u} C]
variable {B : Type u} [CommRing B]
variable [((⊥ : GrothendieckTopology C)).HasSheafCompose (forget₂ CommRingCat RingCat.{u})]
variable [((⊥ : GrothendieckTopology C)).PreservesSheafification
  (forget₂ CommRingCat RingCat.{u})]
variable [((⊥ : GrothendieckTopology C)).WEqualsLocallyBijective AddCommGrpCat.{u}]

local notation "J" => (⊥ : GrothendieckTopology C)

private abbrev bPresheaf
    (C : Type u) [Category.{u} C]
    (B : Type u) [CommRing B] :=
  Cᵒᵖ ⥤ ModuleCat B

private abbrev abPresheaf
    (C : Type u) [Category.{u} C] :=
  Cᵒᵖ ⥤ AddCommGrpCat.{u}

private abbrev constantRingPresheaf
    (C : Type u) [Category.{u} C]
    (B : Type u) [CommRing B] :
    Cᵒᵖ ⥤ RingCat.{u} :=
  (Functor.const Cᵒᵖ).obj (RingCat.of B)

private abbrev qisAbPresheaf
    (C : Type u) [Category.{u} C] :=
  HomotopyCategory.quasiIso (abPresheaf C) (up ℤ)

private abbrev qisBPresheaf
    (C : Type u) [Category.{u} C]
    (B : Type u) [CommRing B] :=
  HomotopyCategory.quasiIso (bPresheaf C B) (up ℤ)

private def constantRingSheafIso
    :
    ringSheaf J ((constantSheaf J CommRingCat.{u}).obj (CommRingCat.of B)) ≅
      (constantSheaf J RingCat.{u}).obj (RingCat.of B) :=
  (constantCommuteCompose J (forget₂ CommRingCat RingCat.{u})).app
    (CommRingCat.of B)

private noncomputable def constantRingPresheafToRingSheaf
    [HasWeakSheafify J RingCat.{u}] :
    constantRingPresheaf C B ⟶
      (ringSheaf J ((constantSheaf J CommRingCat.{u}).obj (CommRingCat.of B))).obj :=
  (show
      constantRingPresheaf C B ⟶
        ((constantSheaf J RingCat.{u}).obj (RingCat.of B)).obj
    by
      simpa [constantSheaf] using
        toSheafify J (constantRingPresheaf C B)) ≫
    constantRingSheafIso.inv.hom

private def constantSheafModuleToConstantPresheafModule
    [HasWeakSheafify J RingCat.{u}] :
    ringedSiteModuleCategory J ((constantSheaf J CommRingCat.{u}).obj (CommRingCat.of B)) ⥤
      PresheafOfModules (constantRingPresheaf C B) :=
  SheafOfModules.forget (ringSheaf J ((constantSheaf J CommRingCat.{u}).obj (CommRingCat.of B))) ⋙
    PresheafOfModules.restrictScalars constantRingPresheafToRingSheaf

/-- The canonical bridge from modules over the constant ring presheaf to `B`-module-valued
presheaves. The ambient owner `PresheafOfModules.toPresheaf` forgets further to abelian
presheaves, so this bridge keeps the `B`-module structure needed by
`categoryOverPointDerivedColimit C (ModuleCat B)`. -/
private noncomputable def constantPresheafToBPresheaf :
    PresheafOfModules (constantRingPresheaf C B) ⥤ bPresheaf C B := {
  obj := fun M ↦ {
    obj := fun X ↦ by
      simpa [constantRingPresheaf] using M.obj X
    map := fun f ↦ by
      simpa [constantRingPresheaf] using M.map f
    map_id := fun X ↦ by
      ext m
      rw [M.map_id]
      change
        (CategoryTheory.ConcreteCategory.hom
          ((ModuleCat.restrictScalarsId'App
            (((constantRingPresheaf C B).map (𝟙 X)).hom)
            (congrArg RingCat.Hom.hom ((constantRingPresheaf C B).map_id X))
            (M.obj X)).inv)) m = m
      exact ModuleCat.restrictScalarsId'App_inv_apply
        (((constantRingPresheaf C B).map (𝟙 X)).hom)
        (congrArg RingCat.Hom.hom ((constantRingPresheaf C B).map_id X))
        (M.obj X) m
    map_comp := fun f g ↦ by
      ext m
      rw [M.map_comp]
      change
        (CategoryTheory.ConcreteCategory.hom
          ((ModuleCat.restrictScalarsComp'App
            (((constantRingPresheaf C B).map f).hom)
            (((constantRingPresheaf C B).map g).hom)
            (((constantRingPresheaf C B).map (f ≫ g)).hom)
            (congrArg RingCat.Hom.hom ((constantRingPresheaf C B).map_comp f g))
            (M.obj _)).inv))
          (((ModuleCat.restrictScalars (((constantRingPresheaf C B).map f).hom)).map (M.map g)).hom
            ((M.map f).hom m)) =
        ((M.map g).hom ((M.map f).hom m))
      simpa [constantRingPresheaf] using
        (ModuleCat.restrictScalarsComp'App_inv_apply
          (((constantRingPresheaf C B).map f).hom)
          (((constantRingPresheaf C B).map g).hom)
          (((constantRingPresheaf C B).map (f ≫ g)).hom)
          (congrArg RingCat.Hom.hom ((constantRingPresheaf C B).map_comp f g))
          (M.obj _)
          (((ModuleCat.restrictScalars (((constantRingPresheaf C B).map f).hom)).map (M.map g)).hom
            ((M.map f).hom m)))
  }
  map := fun φ ↦ {
    app := fun X ↦ by
      simpa [constantRingPresheaf] using φ.app X
    naturality := fun {X Y} f ↦ by
      simpa [constantRingPresheaf] using φ.naturality f
  }
}

private theorem constantSheafModuleToBPresheaf_exact
    [HasWeakSheafify J RingCat.{u}] :
    exactFunctor
      (ringedSiteModuleCategory J ((constantSheaf J CommRingCat.{u}).obj (CommRingCat.of B)))
      (bPresheaf C B)
      (constantSheafModuleToConstantPresheafModule ⋙ constantPresheafToBPresheaf) := by
  sorry

private noncomputable abbrev constantSheafModuleDerivedToBPresheaf
    [HasWeakSheafify J RingCat.{u}] :
    let ConstB : Sheaf J CommRingCat.{u} :=
      (constantSheaf J CommRingCat.{u}).obj (CommRingCat.of B)
    let Y : RingedSite.{u, u} := RingedSite.ofCommRingSheaf J ConstB
    ModuleDerived Y ⥤ DerivedCategory (bPresheaf C B) :=
  let ConstB : Sheaf J CommRingCat.{u} :=
    (constantSheaf J CommRingCat.{u}).obj (CommRingCat.of B)
  let Y : RingedSite.{u, u} := RingedSite.ofCommRingSheaf J ConstB
  letI : Preadditive
      (ModuleCat Y) :=
    (inferInstance : Abelian (ModuleCat Y)).toPreadditive
  letI : Preadditive (bPresheaf C B) :=
    (inferInstance : Abelian (bPresheaf C B)).toPreadditive
  let F : ModuleCat Y ⥤ bPresheaf C B :=
    constantSheafModuleToConstantPresheafModule ⋙
      constantPresheafToBPresheaf
  let hAdd : Functor.Additive F := by
    sorry
  let hExact : exactFunctor _ _ F := by
    simpa [F] using
      (constantSheafModuleToBPresheaf_exact :
        exactFunctor
          (ringedSiteModuleCategory J ((constantSheaf J CommRingCat.{u}).obj (CommRingCat.of B)))
          (bPresheaf C B)
          (constantSheafModuleToConstantPresheafModule ⋙ constantPresheafToBPresheaf))
  letI : F.Additive := hAdd
  letI : PreservesFiniteLimits F := by
    exact (exactFunctor_iff F).mp hExact |>.1
  letI : PreservesFiniteColimits F := by
    exact (exactFunctor_iff F).mp hExact |>.2
  F.mapDerivedCategory

end

section

variable {C : Type u} [Category.{u} C]
variable {B : Type u} [CommRing B]
variable [((⊥ : GrothendieckTopology C)).HasSheafCompose (forget₂ CommRingCat RingCat.{u})]
variable [((⊥ : GrothendieckTopology C)).PreservesSheafification
  (forget₂ CommRingCat RingCat.{u})]
variable [((⊥ : GrothendieckTopology C)).WEqualsLocallyBijective AddCommGrpCat.{u}]

local notation "J" => (⊥ : GrothendieckTopology C)

/- Domain-style sampling for Remark 21.39.13:
- primary domain: same-site change of structure sheaf to the constant `B`-sheaf, followed by the
  derived lower shriek `Lπ!` for the projection from a category with the chaotic topology to a
  point;
- sampled owner declarations:
  `derivedLowerShriekToPoint`,
  `modulePullbackDerived`,
  `ringedSiteStructureMap`,
  `SheafOfModules.unitToPushforwardObjUnit`,
  `categoryOverPointDerivedColimit`,
  `PresheafOfModules.restrictScalars`;
- best owner abstraction: the core owners remain `derivedLowerShriekToPoint`,
  `modulePullbackDerived`, and `categoryOverPointDerivedColimit`; the only local bridge data is the
  exact forgetful passage from modules over the constant ring sheaf on `B` to
  `B`-valued presheaves;
- primitive data: the structure map `β : O ⟶` the constant `B`-sheaf and the constant-ring bridge
  from sheaf modules over that sheaf to `B`-module presheaves;
- derived API: the source-facing factorization functor below and its companion comparison theorem.

Source/core/bridge triage:
- `source-facing`: `derivedLowerShriekThroughBModules` and the factorization theorem;
- `core/canonical`: `derivedLowerShriekToPoint`, `modulePullbackDerived`, and
  `categoryOverPointDerivedColimit`;
- `bridge/view`: `constantPresheafToBPresheaf`, needed because the upstream forgetful owner
  `PresheafOfModules.toPresheaf` lands only in abelian presheaves. -/

/-- The canonical `D(B)`-valued functor of Remark `21.39.13`: tensor an object of
`D(O)` with the constant `B`-sheaf via same-site derived pullback, then apply the Chapter 21 lower
shriek owner `Lπ! : D(B^{--}) ⥤ D(B)`. -/
noncomputable abbrev derivedLowerShriekThroughBModules
    [HasWeakSheafify J RingCat.{u}]
    (O : Sheaf J CommRingCat.{u})
    [HasSheafify J AddCommGrpCat.{u}]
    (beta : O ⟶ ((constantSheaf J CommRingCat.{u}).obj (CommRingCat.of B)))
    [CategoryWithHomology (ringedSiteModuleCategory J O)]
    [CategoryWithHomology
      (ringedSiteModuleCategory J ((constantSheaf J CommRingCat.{u}).obj (CommRingCat.of B)))]
    [Functor.Additive ((sameSiteHom beta)^*)]
    [HasColimitsOfShape Cᵒᵖ (ModuleCat B)]
    [Functor.HasLeftDerivedFunctor
      (categoryOverPointColimitToDerived C (ModuleCat B) :
        HomotopyCategory (bPresheaf C B) (up ℤ) ⥤ DerivedCategory (ModuleCat B))
      (qisBPresheaf C B)]
    [Functor.HasLeftDerivedFunctor
      (modulePullbackToDerived (sameSiteHom beta))
      (ModuleQis (RingedSite.ofCommRingSheaf J O))] :
    DerivedCategory (ringedSiteModuleCategory J O) ⥤
      DerivedCategory (ModuleCat B) :=
  let ConstB : Sheaf J CommRingCat.{u} :=
    (constantSheaf J CommRingCat.{u}).obj (CommRingCat.of B)
  let X : RingedSite.{u, u} := RingedSite.ofCommRingSheaf J O
  let Y : RingedSite.{u, u} := RingedSite.ofCommRingSheaf J ConstB
  let Lpull : ModuleDerived X ⥤ ModuleDerived Y :=
    modulePullbackDerived (sameSiteHom beta)
  let G : ModuleDerived Y ⥤ DerivedCategory (bPresheaf C B) :=
    constantSheafModuleDerivedToBPresheaf
  show DerivedCategory (ringedSiteModuleCategory J O) ⥤ DerivedCategory (ModuleCat B) from by
    simpa [ConstB, X, Y, RingedSite.Hom.ModuleDerived, RingedSite.Hom.ModuleCat,
      ringedSiteModuleCategory, ringSheaf] using
      (Lpull ⋙ G ⋙
        (categoryOverPointDerivedColimit C (ModuleCat B) :
          DerivedCategory (bPresheaf C B) ⥤ DerivedCategory (ModuleCat B)))

-- Proof sketch: the hypothesis is the same canonical unit-module condition that appears in
-- Lemma `21.39.12`, specialized to `β : O ⟶` the constant `B`-sheaf. Under that hypothesis, the
-- abelian lower shriek of `K` agrees with the abelian lower shriek of
-- `K ⊗^{L}_{O}` the constant `B`-sheaf, and the latter is exactly the forgetful image of
-- `derivedLowerShriekThroughBModules`.
/-- Remark 21.39.13: let `β : O ⟶` the constant `B`-sheaf be a morphism of sheaves of commutative
rings on a category with the chaotic topology. If the canonical unit-module map
`SheafOfModules.unitToPushforwardObjUnit (ringedSiteStructureMap β)` becomes an isomorphism after
the abelian lower shriek `Lπ!`, then after forgetting `B`-module structure the canonical functor
`derivedLowerShriekThroughBModules` recovers the abelian lower shriek
`derivedLowerShriekToPoint`.

This file keeps the source-facing comparison at the proposition-level owner `IsIsomorphic`, rather
than choosing a public `Iso` witness from a proof-only comparison theorem. -/
@[stacks 09CZ]
theorem derivedLowerShriekOnAbelianSheaves_factors_through_B_modules
    [HasWeakSheafify J RingCat.{u}]
    (O : Sheaf J CommRingCat.{u})
    [HasSheafify J AddCommGrpCat.{u}]
    [HasColimitsOfShape Cᵒᵖ AddCommGrpCat.{u}]
    (beta : O ⟶ ((constantSheaf J CommRingCat.{u}).obj (CommRingCat.of B)))
    [CategoryWithHomology (ringedSiteModuleCategory J O)]
    [CategoryWithHomology
      (ringedSiteModuleCategory J ((constantSheaf J CommRingCat.{u}).obj (CommRingCat.of B)))]
    [Functor.Additive ((sameSiteHom beta)^*)]
    [Functor.HasLeftDerivedFunctor
      (categoryOverPointColimitToDerived C AddCommGrpCat.{u} :
        HomotopyCategory (abPresheaf C) (up ℤ) ⥤ DerivedCategory AddCommGrpCat.{u})
      (qisAbPresheaf C)]
    [HasColimitsOfShape Cᵒᵖ (ModuleCat B)]
    [Functor.HasLeftDerivedFunctor
      (categoryOverPointColimitToDerived C (ModuleCat B) :
        HomotopyCategory (bPresheaf C B) (up ℤ) ⥤ DerivedCategory (ModuleCat B))
      (qisBPresheaf C B)]
    [Functor.HasLeftDerivedFunctor
      (modulePullbackToDerived (sameSiteHom beta))
      (ModuleQis (RingedSite.ofCommRingSheaf J O))]
    (hbeta : IsIso
      ((derivedLowerShriekToPoint O).map
        ((DerivedCategory.singleFunctor
            (ringedSiteModuleCategory J O) (0 : ℤ)).map
          (SheafOfModules.unitToPushforwardObjUnit (ringedSiteStructureMap beta))))) :
    IsIsomorphic
      (derivedLowerShriekToPoint O)
      ((derivedLowerShriekThroughBModules O beta) ⋙
        (forget₂ (ModuleCat B) AddCommGrpCat.{u}).mapDerivedCategory) := by
  sorry

end

end CategoryTheory.ModulesOnCategory
