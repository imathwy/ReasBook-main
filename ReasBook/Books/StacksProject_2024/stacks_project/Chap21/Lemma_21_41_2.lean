import StacksProject_2024.Chap13.Lemma_13_14_16_Homotopy
import StacksProject_2024.Chap12.Lemma_12_7_2
import StacksProject_2024.Chap18.Lemma_18_14_1
import StacksProject_2024.Chap21.Definition_21_41_1
import StacksProject_2024.Chap21.Lemma_21_18_2
import StacksProject_2024.Chap21.SiteAbelianDerived

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

attribute [local instance] HasDerivedCategory.standard

universe u

namespace CategoryTheory

open RingedSite.Hom
open SheafOfModules.RingedSite
open CategoryTheory.Limits
open scoped CategoryTheory

section

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [HasWeakSheafify (simplicialSite J) CommRingCat]
variable [(simplicialSite J).WEqualsLocallyBijective CommRingCat]
variable [(simplicialSite J).HasSheafCompose (forget₂ CommRingCat RingCat)]

local notation "DMod[" A "]" => DerivedCategory (Mod(A•))

/- Domain-style sampling for Lemma 21.41.2:
- primary domain: simplicial sheaves of modules on the simplicial site `Δ × 𝒞`, together with
  projection lower shriek to `𝒞` and same-site change of structure sheaf along
  `α : A_• ⟶ B_•`;
- sampled owner declarations:
  `CategoryTheory.SimplicialSheafOfModules`,
  `CategoryTheory.simplicialAssociatedRingSheafMap`,
  `(SheafOfModules.toSheaf _).mapDerivedCategory`,
  `CategoryTheory.siteAbelianInverseImageDerived`,
  `RingedSite.Hom.modulePullbackDerived`;
- best owner abstraction: the source-facing category is `Mod(A_•)`; the
  projection lower shriek is the canonical left adjoint to the abelian inverse image along
  `π : Δ × 𝒞 ⥤ 𝒞`, after forgetting module structure, and tensoring along `α` is the same-site
  derived pullback owner
  `modulePullbackDerived (sameSiteHom (simplicialAssociatedRingSheafMap α))`;
- primitive data: `α` and the induced map of associated ring sheaves on the simplicial site;
- derived API: the proposition-level functor and objectwise isomorphism theorems below on the
  actual owner functors.

Source/core/bridge triage:
- `source-facing`: the comparison between `Lπ_!(K)` and
  `Lπ_!(K ⊗^L[α])`;
- `core/canonical`: `SimplicialSheafOfModules`, `(SheafOfModules.toSheaf _).mapDerivedCategory`,
  `siteAbelianInverseImageDerived`, and `modulePullbackDerived`;
- `bridge/view`: `simplicialAssociatedRingSheafMap` and the projection lower-shriek owner below.
-/

section CanonicalOwners

variable [HasSheafify J AddCommGrpCat]
variable [J.WEqualsLocallyBijective AddCommGrpCat]
variable [HasSheafify (simplicialSite J) AddCommGrpCat]
variable [(simplicialSite J).WEqualsLocallyBijective AddCommGrpCat]

variable [Functor.IsContinuous simplicialProjection (simplicialSite J) J]
variable [Functor.IsCocontinuous simplicialProjection (simplicialSite J) J]
variable [Functor.Additive
  (simplicialProjection.sheafPushforwardContinuous AddCommGrpCat.{u} (simplicialSite J) J)]
variable [IsGrothendieckAbelian.{u} (Sheaf J AddCommGrpCat.{u})]

/-- The canonical abelian-valued projection lower shriek
`Lπ_! : D(A_•) ⥤ D(𝒞)` for simplicial modules. -/
abbrev simplicialProjectionDerivedLowerShriek
    (A : SimplicialObject (Sheaf J CommRingCat))
    [hAdd :
      Functor.Additive
      (SheafOfModules.toSheaf
        (ringSheaf (simplicialSite J) (simplicialAssociatedRingSheaf A)))]
    [Functor.IsRightAdjoint
      (siteAbelianInverseImageDerived (simplicialSite J) J simplicialProjection)] :
    DMod[A] ⥤ DerivedCategory (Sheaf J AddCommGrpCat.{u}) :=
  let _ :
      Abelian
        (Mod(ringSheaf (simplicialSite J) (simplicialAssociatedRingSheaf A))) :=
    SheafOfModules.instAbelian
      (ringSheaf (simplicialSite J) (simplicialAssociatedRingSheaf A))
  let _ : Abelian (Sheaf (simplicialSite J) AddCommGrpCat.{u}) :=
    sheafAddCommGrpCat_abelian (simplicialSite J)
  let F :
      Mod(ringSheaf (simplicialSite J) (simplicialAssociatedRingSheaf A)) ⥤
        Sheaf (simplicialSite J) AddCommGrpCat.{u} :=
    SheafOfModules.toSheaf
      (ringSheaf (simplicialSite J) (simplicialAssociatedRingSheaf A))
  let _ : Functor.Additive F := by
    simpa [F] using hAdd
  let hExact :
      exactFunctor
        (Mod(ringSheaf (simplicialSite J) (simplicialAssociatedRingSheaf A)))
        (Sheaf (simplicialSite J) AddCommGrpCat.{u}) F :=
    (ExactFunctor.of F).property
  let _ : PreservesFiniteLimits F := by
    simpa [F] using (exactFunctor_iff F).mp hExact |>.1
  let _ : PreservesFiniteColimits F := by
    simpa [F] using (exactFunctor_iff F).mp hExact |>.2
  F.mapDerivedCategory ⋙
    Functor.leftAdjoint
      (siteAbelianInverseImageDerived (simplicialSite J) J simplicialProjection)

/- Lean surface notation for the recurring projection lower shriek `Lπ_!` on the simplicial site
`Δ × 𝒞`. The simplicial structure sheaf `A_•` is the owner parameter visible on the theorem
surface. -/
scoped notation:max "Lπ![" A:max "]" => simplicialProjectionDerivedLowerShriek A

section

variable {A B : SimplicialObject (Sheaf J CommRingCat)}

variable [Functor.IsRightAdjoint
  (siteAbelianInverseImageDerived (simplicialSite J) J simplicialProjection)]

variable [Functor.Additive
  (SheafOfModules.toSheaf
    (ringSheaf (simplicialSite J) (simplicialAssociatedRingSheaf A)))]
variable [CategoryWithHomology (Mod(A•))]
variable [MonoidalCategory (Mod(A•))]
variable [MonoidalPreadditive (Mod(A•))]
variable [Functor.Additive
  (SheafOfModules.toSheaf
    (ringSheaf (simplicialSite J) (simplicialAssociatedRingSheaf B)))]
variable [CategoryWithHomology (Mod(B•))]
variable [MonoidalCategory (Mod(B•))]
variable [MonoidalPreadditive (Mod(B•))]
variable [((𝟭 (SimplexCategory × C)).sheafPushforwardContinuous
  CommRingCat.{u} (simplicialSite J) (simplicialSite J)).IsRightAdjoint]

namespace SimplicialDerivedTensorChangeOfRings

/- Textbook surface notation for the derived change-of-rings object
`K ⊗^L[α]`, with the structure-sheaf morphism carried explicitly by `α`. -/
set_option quotPrecheck false in
scoped notation:70 K:70 " ⊗^L[" α:70 "]" =>
  Functor.obj
    (modulePullbackDerived (sameSiteHom (simplicialAssociatedRingSheafMap α)))
    K

end SimplicialDerivedTensorChangeOfRings

open scoped SimplicialDerivedTensorChangeOfRings

section

variable (α : A ⟶ B)

local notation "XA" =>
  RingedSite.ofCommRingSheaf (simplicialSite J) (simplicialAssociatedRingSheaf A)
local notation "XB" =>
  RingedSite.ofCommRingSheaf (simplicialSite J) (simplicialAssociatedRingSheaf B)
local notation "fα" =>
  sameSiteHom (simplicialAssociatedRingSheafMap α)
local notation "Lα" =>
  modulePullbackDerived fα
local notation "QhA" =>
  (DerivedCategory.Qh :
    HomotopyCategory (Mod(A•)) (ComplexShape.up ℤ) ⥤ DMod[A])
local notation "QhB" =>
  (DerivedCategory.Qh :
    HomotopyCategory (Mod(B•)) (ComplexShape.up ℤ) ⥤ DMod[B])
local notation "LπAb" =>
  Functor.leftAdjoint
    (siteAbelianInverseImageDerived (simplicialSite J) J simplicialProjection)

private abbrev simplicialChangeOfRingsCounit :
    QhA ⋙ Lα ⟶ modulePullbackToDerived fα :=
  Functor.totalLeftDerivedCounit
    (modulePullbackToDerived fα)
    QhA
    (ModuleQis XA)

private abbrev simplicialUnderlyingAbelianFunctor
    (A : SimplicialObject (Sheaf J CommRingCat)) :
    Mod(A•) ⥤ Sheaf (simplicialSite J) AddCommGrpCat.{u} :=
  SheafOfModules.toSheaf
    (ringSheaf (simplicialSite J) (simplicialAssociatedRingSheaf A))

omit [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
  [HasWeakSheafify (simplicialSite J) CommRingCat]
  [(simplicialSite J).WEqualsLocallyBijective CommRingCat]
  [HasSheafify J AddCommGrpCat]
  [J.WEqualsLocallyBijective AddCommGrpCat]
  [Functor.IsContinuous simplicialProjection (simplicialSite J) J]
  [Functor.IsCocontinuous simplicialProjection (simplicialSite J) J]
  [Functor.Additive
    (simplicialProjection.sheafPushforwardContinuous AddCommGrpCat (simplicialSite J) J)]
  [IsGrothendieckAbelian.{u} (Sheaf J AddCommGrpCat.{u})]
  [Functor.IsRightAdjoint
    (siteAbelianInverseImageDerived (simplicialSite J) J simplicialProjection)]
  [MonoidalCategory (Mod(A•))]
  [MonoidalPreadditive (Mod(A•))]
  [((𝟭 (SimplexCategory × C)).sheafPushforwardContinuous
    CommRingCat.{u} (simplicialSite J) (simplicialSite J)).IsRightAdjoint] in
private theorem simplicialUnderlyingAbelianFunctor_isLeftDerivedFunctor :
    (simplicialUnderlyingAbelianFunctor A).mapDerivedCategory.IsLeftDerivedFunctor
      ((simplicialUnderlyingAbelianFunctor A).mapDerivedCategoryFactorsh.hom)
      (HomotopyCategory.quasiIso (Mod(A•)) (ComplexShape.up ℤ)) := by
  let F := simplicialUnderlyingAbelianFunctor A
  simpa [F, simplicialUnderlyingAbelianFunctor] using
    (Functor.isLeftDerivedFunctor_of_inverts
      (HomotopyCategory.quasiIso (Mod(A•)) (ComplexShape.up ℤ))
      F.mapDerivedCategory
      F.mapDerivedCategoryFactorsh)

private abbrev simplicialUnderlyingAbelianComparison :
    simplicialUnderlyingAbelianFunctor A ⟶
      (fα)^* ⋙ simplicialUnderlyingAbelianFunctor B where
  app M :=
    (simplicialUnderlyingAbelianFunctor A).map
      ((SheafOfModules.pullbackPushforwardAdjunction
        (ringedSiteStructureMap (simplicialAssociatedRingSheafMap α))).unit.app M)
  naturality := by
    intro M N f
    change
      (simplicialUnderlyingAbelianFunctor A).map f ≫
          (simplicialUnderlyingAbelianFunctor A).map
            ((SheafOfModules.pullbackPushforwardAdjunction
              (ringedSiteStructureMap (simplicialAssociatedRingSheafMap α))).unit.app N) =
        (simplicialUnderlyingAbelianFunctor A).map
            ((SheafOfModules.pullbackPushforwardAdjunction
              (ringedSiteStructureMap (simplicialAssociatedRingSheafMap α))).unit.app M) ≫
          (((fα)^* ⋙
            simplicialUnderlyingAbelianFunctor B).map f)
    simpa [simplicialUnderlyingAbelianFunctor, Category.assoc] using
      congrArg
        (fun g ↦ (simplicialUnderlyingAbelianFunctor A).map g)
        (NatTrans.naturality
          ((SheafOfModules.pullbackPushforwardAdjunction
            (ringedSiteStructureMap (simplicialAssociatedRingSheafMap α))).unit)
          f)

private abbrev simplicialUnderlyingAbelianAfterTensorToDerived :
    HomotopyCategory (Mod(A•)) (ComplexShape.up ℤ) ⥤
      DerivedCategory (Sheaf (simplicialSite J) AddCommGrpCat.{u}) :=
  modulePullbackToDerived fα ⋙
    (simplicialUnderlyingAbelianFunctor B).mapDerivedCategory

private abbrev simplicialUnderlyingAbelianAfterTensorCounit :
    QhA ⋙ (Lα ⋙ (simplicialUnderlyingAbelianFunctor B).mapDerivedCategory) ⟶
      simplicialUnderlyingAbelianAfterTensorToDerived α :=
  (Functor.associator
      QhA
      Lα
      (simplicialUnderlyingAbelianFunctor B).mapDerivedCategory).inv ≫
    Functor.whiskerRight
      (simplicialChangeOfRingsCounit α)
      ((simplicialUnderlyingAbelianFunctor B).mapDerivedCategory)

private noncomputable def simplicialUnderlyingAbelianAfterTensorUnderivedComparison :
    ((simplicialUnderlyingAbelianFunctor A).mapHomotopyCategory (ComplexShape.up ℤ)) ⋙
        (DerivedCategory.Qh :
          HomotopyCategory (Sheaf (simplicialSite J) AddCommGrpCat) (ComplexShape.up ℤ) ⥤
            DerivedCategory (Sheaf (simplicialSite J) AddCommGrpCat)) ⟶
      simplicialUnderlyingAbelianAfterTensorToDerived α :=
  Functor.whiskerRight
    (NatTrans.mapHomotopyCategory
      (simplicialUnderlyingAbelianComparison α)
      (ComplexShape.up ℤ))
    (DerivedCategory.Qh :
      HomotopyCategory (Sheaf (simplicialSite J) AddCommGrpCat) (ComplexShape.up ℤ) ⥤
        DerivedCategory (Sheaf (simplicialSite J) AddCommGrpCat)) ≫
    (Functor.isoWhiskerRight
      (Functor.mapHomotopyCategoryCompIso
        ((fα)^*)
        (simplicialUnderlyingAbelianFunctor B))
      (DerivedCategory.Qh :
        HomotopyCategory (Sheaf (simplicialSite J) AddCommGrpCat) (ComplexShape.up ℤ) ⥤
          DerivedCategory (Sheaf (simplicialSite J) AddCommGrpCat))).hom ≫
    (Functor.associator
      (((fα)^*).mapHomotopyCategory (ComplexShape.up ℤ))
      ((simplicialUnderlyingAbelianFunctor B).mapHomotopyCategory (ComplexShape.up ℤ))
      (DerivedCategory.Qh :
        HomotopyCategory (Sheaf (simplicialSite J) AddCommGrpCat) (ComplexShape.up ℤ) ⥤
          DerivedCategory (Sheaf (simplicialSite J) AddCommGrpCat))).hom ≫
    Functor.whiskerLeft
      (((fα)^*).mapHomotopyCategory (ComplexShape.up ℤ))
      ((simplicialUnderlyingAbelianFunctor B).mapDerivedCategoryFactorsh.inv) ≫
    (Functor.associator
      (((fα)^*).mapHomotopyCategory (ComplexShape.up ℤ))
      QhB
      (simplicialUnderlyingAbelianFunctor B).mapDerivedCategory).hom

private theorem simplicialUnderlyingAbelianAfterTensor_isLeftDerivedFunctor :
    (Lα ⋙ (simplicialUnderlyingAbelianFunctor B).mapDerivedCategory).IsLeftDerivedFunctor
      (simplicialUnderlyingAbelianAfterTensorCounit α)
      (HomotopyCategory.quasiIso (Mod(A•)) (ComplexShape.up ℤ)) := by
  -- The target is the exact postcomposition of the canonical left derived pullback by the exact
  -- underlying-abelian-sheaf functor on `Mod(B•)`.
  sorry

/-- The source-facing `Lπ!A_• → Lπ!B_•` comparison of Lemma `21.41.2`, expressed as the
projection lower shriek of the unit-module comparison induced by `α`. -/
abbrev simplicialProjectionDerivedLowerShriekUnitComparison (α : A ⟶ B) :=
  (Lπ![A]).map
    ((DerivedCategory.singleFunctor (Mod(A•)) (0 : ℤ)).map
      (SheafOfModules.unitToPushforwardObjUnit
        (ringedSiteStructureMap (simplicialAssociatedRingSheafMap α))))

/-- Companion functor-level reformulation of Lemma `21.41.2`: after tensoring along `α`, the two
canonical projection lower-shriek functors are isomorphic. -/
theorem simplicialProjectionDerivedLowerShriek_after_tensor_structureSheafChange_functor_isomorphic
    (hα : IsIso (simplicialProjectionDerivedLowerShriekUnitComparison α)) :
    IsIsomorphic Lπ![A] (Lα ⋙ Lπ![B]) := by
  letI :
      (simplicialUnderlyingAbelianFunctor A).mapDerivedCategory.IsLeftDerivedFunctor
        ((simplicialUnderlyingAbelianFunctor A).mapDerivedCategoryFactorsh.hom)
        (HomotopyCategory.quasiIso (Mod(A•)) (ComplexShape.up ℤ)) :=
    simplicialUnderlyingAbelianFunctor_isLeftDerivedFunctor
  letI :
      (Lα ⋙ (simplicialUnderlyingAbelianFunctor B).mapDerivedCategory).IsLeftDerivedFunctor
        (simplicialUnderlyingAbelianAfterTensorCounit α)
        (HomotopyCategory.quasiIso (Mod(A•)) (ComplexShape.up ℤ)) :=
    simplicialUnderlyingAbelianAfterTensor_isLeftDerivedFunctor α
  let η :
      (simplicialUnderlyingAbelianFunctor A).mapDerivedCategory ⟶
        Lα ⋙ (simplicialUnderlyingAbelianFunctor B).mapDerivedCategory :=
    Functor.leftDerivedNatTrans
      ((simplicialUnderlyingAbelianFunctor A).mapDerivedCategory)
      (Lα ⋙ (simplicialUnderlyingAbelianFunctor B).mapDerivedCategory)
      ((simplicialUnderlyingAbelianFunctor A).mapDerivedCategoryFactorsh.hom)
      (simplicialUnderlyingAbelianAfterTensorCounit α)
      (HomotopyCategory.quasiIso (Mod(A•)) (ComplexShape.up ℤ))
      (simplicialUnderlyingAbelianAfterTensorUnderivedComparison α)
  let ηπ : Lπ![A] ⟶ Lα ⋙ Lπ![B] :=
    Functor.whiskerRight η LπAb ≫
      (Functor.associator
        Lα
        (simplicialUnderlyingAbelianFunctor B).mapDerivedCategory
        LπAb).hom
  have hηπ : IsIso ηπ := by
    -- Proof sketch: identify the projection lower shriek on simplicial modules with the canonical
    -- abelian lower shriek along `π : Δ × 𝒞 ⥤ 𝒞` after forgetting module structure. Lemma
    -- `21.40.2` computes this lower shriek fiberwise, and on each fiber the change-of-rings
    -- statement is exactly Lemma `21.39.12` for the structure-sheaf map induced by `α`.
    sorry
  let _ : IsIso ηπ := hηπ
  exact ⟨asIso ηπ⟩

/-- Lemma `21.41.2`: for every `K : D(A_•)`, the canonical projection lower-shriek objects before
and after tensoring along `α` are isomorphic. -/
@[stacks 09D2]
theorem simplicialProjectionDerivedLowerShriek_after_tensor_structureSheafChange_isomorphic
    (hα : IsIso (simplicialProjectionDerivedLowerShriekUnitComparison α))
    (K : DMod[A]) :
    IsIsomorphic ((Lπ![A]).obj K) ((Lπ![B]).obj (K ⊗^L[α])) := by
  obtain ⟨e⟩ :=
    simplicialProjectionDerivedLowerShriek_after_tensor_structureSheafChange_functor_isomorphic
      α hα
  change IsIsomorphic ((Lπ![A]).obj K) ((Lα ⋙ Lπ![B]).obj K)
  exact ⟨e.app K⟩

end

end

end CanonicalOwners

end

end CategoryTheory
