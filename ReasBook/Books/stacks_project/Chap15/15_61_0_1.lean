import Mathlib
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
import stacks_project.Chap15.«15_60_1_1»

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory
open ComplexShape
open scoped TensorProduct DerivedTensorWithAlgebra

universe u

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] Algebra.TensorProduct.leftAlgebra
attribute [local instance] Algebra.TensorProduct.rightAlgebra

namespace CategoryTheory

section

variable {A R Aprime : Type u} [CommRing A] [CommRing R] [CommRing Aprime]
variable [Algebra A R] [Algebra A Aprime]

local notation "Rprime" => (Aprime ⊗[A] R)
local notation "DModA" => DerivedCategory (ModuleCat A)
local notation "DModR" => DerivedCategory (ModuleCat R)
local notation "DModAprime" => DerivedCategory (ModuleCat Aprime)
local notation "DModRprime" => DerivedCategory (ModuleCat Rprime)
local notation "KModR" => HomotopyCategory (ModuleCat R) (up ℤ)
local notation "KModA" => HomotopyCategory (ModuleCat A) (up ℤ)
local notation "KModAprime" => HomotopyCategory (ModuleCat Aprime) (up ℤ)
local notation "KModRprime" => HomotopyCategory (ModuleCat Rprime) (up ℤ)
local notation "QhR" => (DerivedCategory.Qh : KModR ⥤ DModR)
local notation "QhA" => (DerivedCategory.Qh : KModA ⥤ DModA)
local notation "QhAprime" => (DerivedCategory.Qh : KModAprime ⥤ DModAprime)
local notation "QhRprime" => (DerivedCategory.Qh : KModRprime ⥤ DModRprime)
local notation "QisR" => HomotopyCategory.quasiIso (ModuleCat R) (up ℤ)
local notation "QisA" => HomotopyCategory.quasiIso (ModuleCat A) (up ℤ)

private abbrev extendRprime : ModuleCat R ⥤ ModuleCat Rprime :=
  ModuleCat.extendScalars (algebraMap R Rprime)

private abbrev restrictA : ModuleCat R ⥤ ModuleCat A :=
  ModuleCat.restrictScalars (algebraMap A R)

private abbrev restrictAprime : ModuleCat Rprime ⥤ ModuleCat Aprime :=
  ModuleCat.restrictScalars (algebraMap Aprime Rprime)

private abbrev extendAprime : ModuleCat A ⥤ ModuleCat Aprime :=
  ModuleCat.extendScalars (algebraMap A Aprime)

private abbrev extendRprimeToDerived : KModR ⥤ DModRprime :=
  let F : ModuleCat R ⥤ ModuleCat Rprime := extendRprime
  letI : F.Additive :=
    (ModuleCat.extendRestrictScalarsAdj.{u, u, u} (algebraMap R Rprime)).left_adjoint_additive
  mapHomotopyCategoryToDerived F

private abbrev extendAprimeToDerived : KModA ⥤ DModAprime :=
  let F : ModuleCat A ⥤ ModuleCat Aprime := extendAprime
  letI : F.Additive :=
    (ModuleCat.extendRestrictScalarsAdj.{u, u, u} (algebraMap A Aprime)).left_adjoint_additive
  mapHomotopyCategoryToDerived F

private abbrev sourceDerived : DModR ⥤ DModAprime :=
  (derivedTensorWithAlgebra (algebraMap R Rprime) : DModR ⥤ DModRprime) ⋙
    (restrictAprime).mapDerivedCategory

private abbrev targetDerived : DModR ⥤ DModAprime :=
  (restrictA).mapDerivedCategory ⋙
    (derivedTensorWithAlgebra (algebraMap A Aprime) : DModA ⥤ DModAprime)

private abbrev extendHot : KModR ⥤ KModRprime :=
  let F : ModuleCat R ⥤ ModuleCat Rprime := extendRprime
  letI : F.Additive :=
    (ModuleCat.extendRestrictScalarsAdj.{u, u, u} (algebraMap R Rprime)).left_adjoint_additive
  F.mapHomotopyCategory (up ℤ)

private abbrev restrictHot : KModR ⥤ KModA :=
  let F : ModuleCat R ⥤ ModuleCat A := restrictA
  letI : F.Additive := by infer_instance
  F.mapHomotopyCategory (up ℤ)

private abbrev restrictAprimeHot : KModRprime ⥤ KModAprime :=
  let F : ModuleCat Rprime ⥤ ModuleCat Aprime := restrictAprime
  letI : F.Additive := by infer_instance
  F.mapHomotopyCategory (up ℤ)

private abbrev extendAprimeHot : KModA ⥤ KModAprime :=
  let F : ModuleCat A ⥤ ModuleCat Aprime := extendAprime
  letI : F.Additive :=
    (ModuleCat.extendRestrictScalarsAdj.{u, u, u} (algebraMap A Aprime)).left_adjoint_additive
  F.mapHomotopyCategory (up ℤ)

private abbrev sourceHot : KModR ⥤ DModAprime :=
  (extendHot : KModR ⥤ KModRprime) ⋙
    (restrictAprimeHot : KModRprime ⥤ KModAprime) ⋙
    (QhAprime : KModAprime ⥤ DModAprime)

private abbrev targetHot : KModR ⥤ DModAprime :=
  (restrictHot : KModR ⥤ KModA) ⋙
    (extendAprimeHot : KModA ⥤ KModAprime) ⋙
    (QhAprime : KModAprime ⥤ DModAprime)

private noncomputable def restrictScalarsSelfEquiv
    (S T : Type u) [CommRing S] [CommRing T] [Algebra S T] :
    ↑((ModuleCat.restrictScalars (algebraMap S T)).obj (ModuleCat.of T T)) ≃ₗ[T] T :=
  { __ := AddEquiv.refl T
    map_smul' := fun _ _ ↦ rfl }

private instance restrictScalarsSelfIsScalarTower
    (S T : Type u) [CommRing S] [CommRing T] [Algebra S T] :
    IsScalarTower S T
      ↑((ModuleCat.restrictScalars (algebraMap S T)).obj (ModuleCat.of T T)) :=
  IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl

private noncomputable abbrev restrictOfIso
    {S T M : Type u} [CommRing S] [CommRing T] [Algebra S T]
    [AddCommGroup M] [Module T M] [Module S M] [IsScalarTower S T M] :
    (ModuleCat.restrictScalars (algebraMap S T)).obj (ModuleCat.of T M) ≅ ModuleCat.of S M :=
  (show ↑((ModuleCat.restrictScalars (algebraMap S T)).obj (ModuleCat.of T M)) ≃ₗ[S] M from
      { __ := AddEquiv.refl _
        map_smul' := fun _ _ ↦ by simp }).toModuleIso

/- Domain-style sampling for 15.61.0.1:
- primary domain: derived base change for module categories over a pushout of commutative rings;
- sampled owner declarations:
  `derivedTensorWithAlgebra`,
  `(ModuleCat.restrictScalars _).mapDerivedCategory`,
  `Functor.leftDerivedNatTrans`,
  `(ModuleCat.restrictScalars _).mapDerivedCategoryFactorsh`;
- best owner abstraction: the core owners are the derived scalar-extension functors
  `derivedTensorWithAlgebra σRprime` and `derivedTensorWithAlgebra σAprime`, the exact restriction
  functors induced on derived categories by
  `ModuleCat.restrictScalars`, and the canonical owner comparison morphism
  `Functor.leftDerivedNatTrans` between the resulting left derived functors;
- primitive data: the algebra maps `A → R`, `A → A'`, the tensor-product ring
  `R' = A' ⊗[A] R`, the four module-level scalar-change functors
  `extendRprime`, `restrictA`, `restrictAprime`, `extendAprime`, and the exact module-level
  base-change isomorphism between their two composite views;
- derived API: the owner comparison morphism between the two canonical functors
  `sourceDerived` and `targetDerived`, together with its pointwise value at
  `K : D(R)`.

Source/core/bridge triage:
- `source-facing`: the base-change comparison morphism for a fixed `K : D(R)`;
- `core/canonical`: `sourceDerived`, `targetDerived`, and `Functor.leftDerivedNatTrans`;
- `bridge/view`: the pointwise morphism is obtained by evaluating the owner natural
  transformation at `K`. -/

/-- The comparison from `Qh_R ⋙ (- ⊗_R^L R')` followed by restriction to `A'`
to the homotopy-level extension-of-scalars source functor. -/
private noncomputable def sourceCounit
    :
    QhR ⋙
        ((derivedTensorWithAlgebra (algebraMap R Rprime) : DModR ⥤ DModRprime) ⋙
          (restrictAprime).mapDerivedCategory) ⟶
      ((extendHot : KModR ⥤ KModRprime) ⋙
        (restrictAprimeHot : KModRprime ⥤ KModAprime) ⋙
        (QhAprime : KModAprime ⥤ DModAprime)) :=
  letI :
      (extendRprimeToDerived : KModR ⥤ DModRprime).HasLeftDerivedFunctor QisR := by
    simpa [extendRprimeToDerived] using
      extendScalarsToDerived_hasLeftDerivedFunctor (algebraMap R Rprime)
  let hCounit :
      QhR ⋙ (derivedTensorWithAlgebra (algebraMap R Rprime) : DModR ⥤ DModRprime) ⟶
        extendHot ⋙ QhRprime := by
    simpa [extendRprimeToDerived] using
      ((extendRprimeToDerived : KModR ⥤ DModRprime).totalLeftDerivedCounit QhR QisR)
  letI : Limits.PreservesFiniteLimits (restrictAprime : ModuleCat Rprime ⥤ ModuleCat Aprime) := by
    infer_instance
  let hRestrict :
      QhRprime ⋙ (restrictAprime).mapDerivedCategory ⟶ restrictAprimeHot ⋙ QhAprime := by
    simpa [restrictAprimeHot] using
      (((restrictAprime).mapDerivedCategoryFactorsh.hom) :
        QhRprime ⋙ (restrictAprime).mapDerivedCategory ⟶
          restrictAprimeHot ⋙ QhAprime)
  (Functor.associator
      QhR
      (derivedTensorWithAlgebra (algebraMap R Rprime) : DModR ⥤ DModRprime)
      (restrictAprime).mapDerivedCategory).inv ≫
    Functor.whiskerRight hCounit (restrictAprime).mapDerivedCategory ≫
    (Functor.associator extendHot QhRprime (restrictAprime).mapDerivedCategory).hom ≫
    Functor.whiskerLeft extendHot hRestrict ≫
    (Functor.associator extendHot restrictAprimeHot QhAprime).inv

/-- The comparison from `Qh_R ⋙ (-|_A ⊗_A^L A')` to the homotopy-level target functor. -/
private noncomputable def targetCounit
    :
    QhR ⋙
        ((restrictA).mapDerivedCategory ⋙
          (derivedTensorWithAlgebra (algebraMap A Aprime) : DModA ⥤ DModAprime)) ⟶
      ((restrictHot : KModR ⥤ KModA) ⋙
        (extendAprimeHot : KModA ⥤ KModAprime) ⋙
        (QhAprime : KModAprime ⥤ DModAprime)) :=
  let hCounit :
      QhA ⋙ (derivedTensorWithAlgebra (algebraMap A Aprime) : DModA ⥤ DModAprime) ⟶
        extendAprimeHot ⋙ QhAprime := by
    letI :
        (extendAprimeToDerived : KModA ⥤ DModAprime).HasLeftDerivedFunctor QisA := by
      simpa [extendAprimeToDerived] using
        extendScalarsToDerived_hasLeftDerivedFunctor (algebraMap A Aprime)
    simpa [extendAprimeToDerived] using
      ((extendAprimeToDerived : KModA ⥤ DModAprime).totalLeftDerivedCounit
        QhA
        QisA)
  letI : Limits.PreservesFiniteLimits (restrictA : ModuleCat R ⥤ ModuleCat A) := by
    infer_instance
  let hRestrict : QhR ⋙ (restrictA).mapDerivedCategory ⟶ restrictHot ⋙ QhA := by
    simpa [restrictHot] using
      (((restrictA).mapDerivedCategoryFactorsh.hom) :
        QhR ⋙ (restrictA).mapDerivedCategory ⟶
          restrictHot ⋙ QhA)
  (Functor.associator
      QhR
      (restrictA).mapDerivedCategory
      (derivedTensorWithAlgebra (algebraMap A Aprime) : DModA ⥤ DModAprime)).hom ≫
    Functor.whiskerRight hRestrict
      (derivedTensorWithAlgebra (algebraMap A Aprime) : DModA ⥤ DModAprime) ≫
    (Functor.associator
      restrictHot
      QhA
      (derivedTensorWithAlgebra (algebraMap A Aprime) : DModA ⥤ DModAprime)).inv ≫
    Functor.whiskerLeft restrictHot hCounit ≫
    (Functor.associator restrictHot extendAprimeHot QhAprime).inv

/-- Postcomposing the derived extension functor `- ⊗_R^{\mathbf L} R'` with exact restriction to
`A'` still exhibits a left derived functor of the corresponding homotopy-level source functor. -/
private theorem sourceCounit_isLeftDerivedFunctor
    :
    (((derivedTensorWithAlgebra (algebraMap R Rprime) : DModR ⥤ DModRprime) ⋙
      (restrictAprime).mapDerivedCategory)).IsLeftDerivedFunctor sourceCounit QisR := by
  sorry

/-- The target underived functor factors through the localization `Qh_R`, so
`-|_A ⊗_A^L A'` is its left derived functor. -/
private theorem targetCounit_isLeftDerivedFunctor
    :
    (((restrictA).mapDerivedCategory ⋙
      (derivedTensorWithAlgebra (algebraMap A Aprime) : DModA ⥤ DModAprime))).IsLeftDerivedFunctor
      targetCounit
      QisR := by
  sorry

attribute [local instance] sourceCounit_isLeftDerivedFunctor targetCounit_isLeftDerivedFunctor

/-- The exact module-level base-change isomorphism
`(A' ⊗[A] R) ⊗[R] M ≅ A' ⊗[A] M`. -/
private noncomputable def baseChangeModuleIso
    :
    (extendRprime : ModuleCat R ⥤ ModuleCat Rprime) ⋙
        (restrictAprime : ModuleCat Rprime ⥤ ModuleCat Aprime) ≅
      (restrictA : ModuleCat R ⥤ ModuleCat A) ⋙
        (extendAprime : ModuleCat A ⥤ ModuleCat Aprime) :=
  NatIso.ofComponents
    (fun (M : ModuleCat R) ↦ by
      let _ : Module A (M : Type u) := Module.compHom (M : Type u) (algebraMap A R)
      let _ : IsScalarTower A R (M : Type u) := IsScalarTower.of_compHom A R (M : Type u)
      let eLeftRprime :
          (extendRprime).obj M ≅ ModuleCat.of Rprime ((Aprime ⊗[A] R) ⊗[R] (M : Type u)) := by
        simpa [extendRprime, ModuleCat.extendScalars, ModuleCat.ExtendScalars.obj'] using
          (TensorProduct.AlgebraTensorModule.congr
            (restrictScalarsSelfEquiv R Rprime)
            (LinearEquiv.refl R (M : Type u))).toModuleIso
      let eLeft :
          (restrictAprime).obj ((extendRprime).obj M) ≅
            ModuleCat.of Aprime ((Aprime ⊗[A] R) ⊗[R] (M : Type u)) := by
        exact (restrictAprime).mapIso eLeftRprime ≪≫
          restrictOfIso
      let eRight :
          (extendAprime).obj ((restrictA).obj M) ≅
            ModuleCat.of Aprime (Aprime ⊗[A] (M : Type u)) := by
        simpa [restrictA, extendAprime, ModuleCat.extendScalars, ModuleCat.ExtendScalars.obj']
          using
            ((TensorProduct.AlgebraTensorModule.congr
              (restrictScalarsSelfEquiv A Aprime)
              (LinearEquiv.refl A ↑((restrictA).obj M))).toModuleIso)
      exact eLeft ≪≫
        (Algebra.IsPushout.cancelBaseChange A Aprime R Rprime (M : Type u)).toModuleIso ≪≫
        eRight.symm)
    (fun _ ↦ by
      sorry)

/-- The homotopy-level base-change comparison between the two canonical scalar-extension
functors. -/
private noncomputable def baseChangeHomotopyIso
    :
    ((extendHot : KModR ⥤ KModRprime) ⋙
      (restrictAprimeHot : KModRprime ⥤ KModAprime) ⋙
      (QhAprime : KModAprime ⥤ DModAprime)) ≅
      ((restrictHot : KModR ⥤ KModA) ⋙
        (extendAprimeHot : KModA ⥤ KModAprime) ⋙
        (QhAprime : KModAprime ⥤ DModAprime)) :=
  let F₁ : ModuleCat R ⥤ ModuleCat Rprime := extendRprime
  let F₂ : ModuleCat Rprime ⥤ ModuleCat Aprime := restrictAprime
  let G₁ : ModuleCat R ⥤ ModuleCat A := restrictA
  let G₂ : ModuleCat A ⥤ ModuleCat Aprime := extendAprime
  letI : F₁.Additive :=
    (ModuleCat.extendRestrictScalarsAdj.{u, u, u} (algebraMap R Rprime)).left_adjoint_additive
  letI : F₂.Additive := by infer_instance
  letI : G₁.Additive := by infer_instance
  letI : G₂.Additive :=
    (ModuleCat.extendRestrictScalarsAdj.{u, u, u} (algebraMap A Aprime)).left_adjoint_additive
  letI : (F₁ ⋙ F₂).Additive := by infer_instance
  letI : (G₁ ⋙ G₂).Additive := by infer_instance
  (Functor.isoWhiskerRight
      (Functor.mapHomotopyCategoryCompIso F₁ F₂).symm
      QhAprime) ≪≫
    Functor.isoWhiskerRight
      (Functor.mapHomotopyCategoryIso baseChangeModuleIso)
      QhAprime ≪≫
    (Functor.isoWhiskerRight
      (Functor.mapHomotopyCategoryCompIso G₁ G₂)
      QhAprime)

/-- The owner comparison morphism for `15.61.0.1`, obtained by deriving the homotopy-level
base-change isomorphism between the two canonical scalar-extension functors. -/
private noncomputable def derivedTensorBaseChangeComparison
    :
    ((derivedTensorWithAlgebra (algebraMap R Rprime) : DModR ⥤ DModRprime) ⋙
      (restrictAprime).mapDerivedCategory) ⟶
      ((restrictA).mapDerivedCategory ⋙
        (derivedTensorWithAlgebra (algebraMap A Aprime) : DModA ⥤ DModAprime)) :=
  Functor.leftDerivedNatTrans
    sourceDerived
    targetDerived
    sourceCounit
    targetCounit
    QisR
    baseChangeHomotopyIso.hom

variable (A Aprime)

/-- The source-facing derived base-change comparison
`(K ⊗_R^{\mathbf L} (A' ⊗[A] R))|_{A'} ⟶ (K|_A) ⊗_A^{\mathbf L} A'`. -/
noncomputable def derivedTensorBaseChange
    (K : DModR) :
    ((ModuleCat.restrictScalars (algebraMap Aprime Rprime)).mapDerivedCategory).obj
        (K ⊗[R]^L[Rprime]) ⟶
      (((ModuleCat.restrictScalars (algebraMap A R)).mapDerivedCategory).obj K) ⊗[A]^L[Aprime] :=
  (derivedTensorBaseChangeComparison.app K)

/-- The derived base-change comparison is the hom of the canonical isomorphism between the two
derived scalar-extension constructions. -/
noncomputable def derivedTensorBaseChangeIso
    (K : DModR) :
    ((ModuleCat.restrictScalars (algebraMap Aprime Rprime)).mapDerivedCategory).obj
        (K ⊗[R]^L[Rprime]) ≅
      (((ModuleCat.restrictScalars (algebraMap A R)).mapDerivedCategory).obj K) ⊗[A]^L[Aprime] :=
  let F : DModR ⥤ DModAprime := sourceDerived
  let G : DModR ⥤ DModAprime := targetDerived
  let e : F ≅ G :=
    Functor.leftDerivedNatIso
      F
      G
      sourceCounit
      targetCounit
      QisR
      baseChangeHomotopyIso
  e.app K

@[simp] theorem derivedTensorBaseChangeIso_hom
    (K : DModR) :
    (derivedTensorBaseChangeIso A Aprime K).hom = derivedTensorBaseChange A Aprime K :=
  rfl

end

end CategoryTheory
