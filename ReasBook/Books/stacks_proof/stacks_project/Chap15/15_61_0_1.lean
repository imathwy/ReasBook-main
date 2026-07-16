import Mathlib
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
import stacks_proof.stacks_project.Chap12.Remark_12_29_2
import stacks_proof.stacks_project.Chap13.Situation_13_15_1
import stacks_proof.stacks_project.Chap15.«15_60_1_1»

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

/-- Helper for 15.61.0.1: extension of scalars from `R` to `A' ⊗[A] R` is additive. -/
local instance extendRprime_additive :
    (ModuleCat.extendScalars.{u, u, u} (algebraMap R Rprime)).Additive :=
  (ModuleCat.extendRestrictScalarsAdj.{u, u, u}
    (algebraMap R Rprime)).left_adjoint_additive

/-- Helper for 15.61.0.1: extension of scalars from `A` to `A'` is additive. -/
local instance extendAprime_additive :
    (ModuleCat.extendScalars.{u, u, u} (algebraMap A Aprime)).Additive :=
  (ModuleCat.extendRestrictScalarsAdj.{u, u, u}
    (algebraMap A Aprime)).left_adjoint_additive

-- Route correction: use the public Chapter 13 owner for the homotopy-to-derived bridge, rather
-- than the private local copy from the scalar-extension file.
private abbrev extendRprimeToDerived : KModR ⥤ DModRprime :=
  let F : ModuleCat R ⥤ ModuleCat Rprime := extendRprime
  letI : F.Additive :=
    (ModuleCat.extendRestrictScalarsAdj.{u, u, u} (algebraMap R Rprime)).left_adjoint_additive
  CategoryTheory.mapHomotopyCategoryToDerived F

private abbrev extendAprimeToDerived : KModA ⥤ DModAprime :=
  let F : ModuleCat A ⥤ ModuleCat Aprime := extendAprime
  letI : F.Additive :=
    (ModuleCat.extendRestrictScalarsAdj.{u, u, u} (algebraMap A Aprime)).left_adjoint_additive
  CategoryTheory.mapHomotopyCategoryToDerived F

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

/-- Helper for 15.61.0.1: the canonical restriction-of-scalars identification acts as the
identity on elements. -/
private theorem restrictOfIso_hom_apply
    {S T M : Type u} [CommRing S] [CommRing T] [Algebra S T]
    [AddCommGroup M] [Module T M] [Module S M] [IsScalarTower S T M]
    (m : (ModuleCat.restrictScalars (algebraMap S T)).obj (ModuleCat.of T M)) :
    (restrictOfIso (S := S) (T := T) (M := M)).hom m = m := rfl

/-- Helper for 15.61.0.1: the inverse restriction-of-scalars identification also acts as the
identity on elements. -/
private theorem restrictOfIso_inv_apply
    {S T M : Type u} [CommRing S] [CommRing T] [Algebra S T]
    [AddCommGroup M] [Module T M] [Module S M] [IsScalarTower S T M]
    (m : M) :
    (restrictOfIso (S := S) (T := T) (M := M)).inv m = m := rfl

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
    -- Exact restriction of scalars preserves finite limits, which is the input needed for
    -- `mapDerivedCategoryFactorsh`.
    exact ((exactFunctor_iff (restrictAprime : ModuleCat Rprime ⥤ ModuleCat Aprime)).1
      (restrictScalars_exact (algebraMap Aprime Rprime))).1
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

/-- Helper for 15.61.0.1: exact restriction of scalars on homotopy categories is already its own
left derived functor. -/
private theorem restrictScalars_mapDerivedCategoryh_isLeftDerivedFunctor
    {S T : Type u} [CommRing S] [CommRing T] [Algebra S T] :
    ((ModuleCat.restrictScalars (algebraMap S T)).mapDerivedCategory).IsLeftDerivedFunctor
      ((ModuleCat.restrictScalars (algebraMap S T)).mapDerivedCategoryFactorsh.hom)
      (HomotopyCategory.quasiIso (ModuleCat T) (up ℤ)) := by
  let F : ModuleCat T ⥤ ModuleCat S := ModuleCat.restrictScalars (algebraMap S T)
  letI : Limits.PreservesFiniteLimits F := by
    infer_instance
  -- Exact restriction preserves quasi-isomorphisms, so the localization comparison is already
  -- the required left-derived counit.
  simpa [F] using
    (Functor.isLeftDerivedFunctor_of_inverts
      (HomotopyCategory.quasiIso (ModuleCat T) (up ℤ))
      F.mapDerivedCategory
      F.mapDerivedCategoryFactorsh)

attribute [local instance] restrictScalars_mapDerivedCategoryh_isLeftDerivedFunctor

/-- Helper for 15.61.0.1: restriction of scalars from `A' ⊗[A] R` to `A'` is exact, hence its
derived-category functor is available. -/
private instance restrictAprime_preservesFiniteLimits :
    Limits.PreservesFiniteLimits (restrictAprime : ModuleCat Rprime ⥤ ModuleCat Aprime) := by
  let F : ModuleCat Rprime ⥤ ModuleCat Aprime :=
    ModuleCat.restrictScalars (algebraMap Aprime Rprime)
  exact ((exactFunctor_iff F).1 (restrictScalars_exact (algebraMap Aprime Rprime))).1

/-- Helper for 15.61.0.1: restriction of scalars from `R` to `A` is exact, hence its
derived-category functor is available. -/
private instance restrictA_preservesFiniteLimits :
    Limits.PreservesFiniteLimits (restrictA : ModuleCat R ⥤ ModuleCat A) := by
  let F : ModuleCat R ⥤ ModuleCat A :=
    ModuleCat.restrictScalars (algebraMap A R)
  exact ((exactFunctor_iff F).1 (restrictScalars_exact (algebraMap A R))).1

/-- Helper for 15.61.0.1: the exact restriction comparison from the homotopy category of
`R'`-modules to the derived category of `A'`-modules is an isomorphism. -/
private instance restrictAprime_mapDerivedCategoryFactorsh_isIso :
    IsIso
      (((restrictAprime).mapDerivedCategoryFactorsh.hom) :
        QhRprime ⋙ (restrictAprime).mapDerivedCategory ⟶
          restrictAprimeHot ⋙ QhAprime) := by
  simpa using
    (show IsIso ((restrictAprime).mapDerivedCategoryFactorsh.hom) from inferInstance)

/-- Helper for 15.61.0.1: the exact restriction comparison from the homotopy category of
`R`-modules to the derived category of `A`-modules is an isomorphism. -/
private instance restrictA_mapDerivedCategoryFactorsh_isIso :
    IsIso
      (((restrictA).mapDerivedCategoryFactorsh.hom) :
        QhR ⋙ (restrictA).mapDerivedCategory ⟶
          restrictHot ⋙ QhA) := by
  simpa using
    (show IsIso ((restrictA).mapDerivedCategoryFactorsh.hom) from inferInstance)

/-- Helper for 15.61.0.1: postcomposing derived extension along `R → R'` with exact restriction
identifies the postcomposed underived source functor with `sourceHot`. -/
private noncomputable def source_postcompose_iso :
    ((extendHot : KModR ⥤ KModRprime) ⋙
      QhRprime ⋙
      (restrictAprime).mapDerivedCategory) ≅
      sourceHot (A := A) (R := R) (Aprime := Aprime) :=
  (Functor.associator
      (extendHot : KModR ⥤ KModRprime)
      QhRprime
      (restrictAprime).mapDerivedCategory) ≪≫
    Functor.isoWhiskerLeft
      (extendHot : KModR ⥤ KModRprime)
      (restrictAprime).mapDerivedCategoryFactorsh ≪≫
    (Functor.associator
      (extendHot : KModR ⥤ KModRprime)
      restrictAprimeHot
      QhAprime).symm

/-- Helper for 15.61.0.1: precomposing exact restriction to `A` with the localization `Qh_R`
identifies `Qh_R ⋙ targetDerived` with the exact-precompose source used in `targetCounit`. -/
private noncomputable def target_precompose_iso :
    QhR ⋙ ((restrictA).mapDerivedCategory ⋙
      (derivedTensorWithAlgebra (algebraMap A Aprime) : DModA ⥤ DModAprime)) ≅
      (restrictHot : KModR ⥤ KModA) ⋙
        QhA ⋙
        (derivedTensorWithAlgebra (algebraMap A Aprime) : DModA ⥤ DModAprime) :=
  (Functor.associator
      QhR
      (restrictA).mapDerivedCategory
      (derivedTensorWithAlgebra (algebraMap A Aprime) : DModA ⥤ DModAprime)) ≪≫
    Functor.isoWhiskerRight
      (restrictA).mapDerivedCategoryFactorsh
      (derivedTensorWithAlgebra (algebraMap A Aprime) : DModA ⥤ DModAprime)

/-- Helper for 15.61.0.1: the source homotopy-level scalar-change route is canonically the
homotopy image of the composite exact module functor followed by localization. -/
private noncomputable def sourceHot_compIso :
    sourceHot (A := A) (R := R) (Aprime := Aprime) ≅
      ((((extendRprime : ModuleCat R ⥤ ModuleCat Rprime) ⋙
          (restrictAprime : ModuleCat Rprime ⥤ ModuleCat Aprime)).mapHomotopyCategory
            (up ℤ)) ⋙
        (QhAprime : KModAprime ⥤ DModAprime)) :=
  (Functor.associator extendHot restrictAprimeHot QhAprime).symm ≪≫
    Functor.isoWhiskerRight
      (Functor.mapHomotopyCategoryCompIso
        (extendRprime : ModuleCat R ⥤ ModuleCat Rprime)
        (restrictAprime : ModuleCat Rprime ⥤ ModuleCat Aprime)).symm
      QhAprime

/-- Helper for 15.61.0.1: the target homotopy-level scalar-change route is canonically the
homotopy image of the composite exact module functor followed by localization. -/
private noncomputable def targetHot_compIso :
    targetHot (A := A) (R := R) (Aprime := Aprime) ≅
      ((((restrictA : ModuleCat R ⥤ ModuleCat A) ⋙
          (extendAprime : ModuleCat A ⥤ ModuleCat Aprime)).mapHomotopyCategory
            (up ℤ)) ⋙
        (QhAprime : KModAprime ⥤ DModAprime)) :=
  (Functor.associator restrictHot extendAprimeHot QhAprime).symm ≪≫
    Functor.isoWhiskerRight
      (Functor.mapHomotopyCategoryCompIso
        (restrictA : ModuleCat R ⥤ ModuleCat A)
        (extendAprime : ModuleCat A ⥤ ModuleCat Aprime)).symm
      QhAprime

/-- Postcomposing the derived extension functor `- ⊗_R^{\mathbf L} R'` with exact restriction to
`A'` still exhibits a left derived functor of the corresponding homotopy-level source functor. -/
private theorem sourceCounit_eq_exact_postcompose_counit
    :
    sourceCounit (A := A) (R := R) (Aprime := Aprime) =
      (by
        letI :
            Limits.PreservesFiniteLimits (restrictAprime : ModuleCat Rprime ⥤ ModuleCat Aprime) := by
          -- Exact restriction of scalars preserves finite limits, so the derived comparison is
          -- available without further transport.
          exact ((exactFunctor_iff (restrictAprime : ModuleCat Rprime ⥤ ModuleCat Aprime)).1
            (restrictScalars_exact (algebraMap Aprime Rprime))).1
        exact
          (Functor.associator
              QhR
              (derivedTensorWithAlgebra (algebraMap R Rprime) : DModR ⥤ DModRprime)
              (restrictAprime).mapDerivedCategory).inv ≫
            Functor.whiskerRight
              (by
                letI :
                    (extendRprimeToDerived : KModR ⥤ DModRprime).HasLeftDerivedFunctor QisR := by
                  simpa [extendRprimeToDerived] using
                    extendScalarsToDerived_hasLeftDerivedFunctor (algebraMap R Rprime)
                -- This is the canonical counit for deriving `extendHot`.
                simpa [extendRprimeToDerived] using
                  ((extendRprimeToDerived : KModR ⥤ DModRprime).totalLeftDerivedCounit QhR QisR))
              (restrictAprime).mapDerivedCategory ≫
            (Functor.associator extendHot QhRprime (restrictAprime).mapDerivedCategory).hom ≫
            Functor.whiskerLeft extendHot
              (by
                -- Exact restriction identifies the derived restriction with the homotopy-level one.
                simpa [restrictAprimeHot] using
                  (((restrictAprime).mapDerivedCategoryFactorsh.hom) :
                    QhRprime ⋙ (restrictAprime).mapDerivedCategory ⟶
                      restrictAprimeHot ⋙ QhAprime)) ≫
            (Functor.associator extendHot restrictAprimeHot QhAprime).inv) := by
  -- This is just the explicit definition of `sourceCounit`.
  rfl

/-- Helper for 15.61.0.1: the scalar-extension route to `D(R')` already has the canonical left
derived functor structure used on the source side. -/
private theorem source_extension_hasLeftDerivedFunctor :
    (extendRprimeToDerived : KModR ⥤ DModRprime).HasLeftDerivedFunctor QisR := by
  -- This is the standard derived scalar-extension existence result specialized to `R → R'`.
  simpa [extendRprimeToDerived] using
    extendScalarsToDerived_hasLeftDerivedFunctor (algebraMap R Rprime)

/-- Helper for 15.61.0.1: this is the exact-postcomposition counit before packaging exact
restriction by `source_postcompose_iso`. -/
private noncomputable def source_exact_postcompose_counit
    :
    QhR ⋙
        ((derivedTensorWithAlgebra (algebraMap R Rprime) : DModR ⥤ DModRprime) ⋙
          (restrictAprime).mapDerivedCategory) ⟶
      ((extendHot : KModR ⥤ KModRprime) ⋙
        QhRprime ⋙
        (restrictAprime).mapDerivedCategory) :=
  letI :
      (extendRprimeToDerived : KModR ⥤ DModRprime).HasLeftDerivedFunctor QisR :=
    source_extension_hasLeftDerivedFunctor (A := A) (R := R) (Aprime := Aprime)
  (Functor.associator
      QhR
      (derivedTensorWithAlgebra (algebraMap R Rprime) : DModR ⥤ DModRprime)
      (restrictAprime).mapDerivedCategory).inv ≫
    Functor.whiskerRight
      (by
        -- This is the canonical counit for deriving `extendHot`.
        simpa [extendRprimeToDerived] using
          ((extendRprimeToDerived : KModR ⥤ DModRprime).totalLeftDerivedCounit QhR QisR))
      (restrictAprime).mapDerivedCategory

/-- Helper for 15.61.0.1: after packaging exact restriction by `source_postcompose_iso`, the
canonical postcomposed total-left-derived counit is exactly `sourceCounit`. -/
private theorem source_exact_postcompose_counit_comp_eq_sourceCounit
    :
    source_exact_postcompose_counit (A := A) (R := R) (Aprime := Aprime) ≫
        (source_postcompose_iso (A := A) (R := R) (Aprime := Aprime)).hom =
      sourceCounit (A := A) (R := R) (Aprime := Aprime) := by
  -- Unfold `sourceCounit` once; the remaining composite is definitionally the packaged
  -- postcomposition iso used on the left.
  -- TODO: normalize the associator/whiskering packaging explicitly so the postcompose iso
  -- collapses to the `sourceCounit` definition.
  sorry

/-- Helper for 15.61.0.1: the exact-postcomposed scalar-extension counit is the right Kan
extension obtained by postcomposing the canonical scalar-extension witness with exact restriction
to `A'`. -/
private theorem source_exact_postcompose_isRightKanExtension
    :
    ((derivedTensorWithAlgebra (algebraMap R Rprime) : DModR ⥤ DModRprime) ⋙
      (restrictAprime).mapDerivedCategory).IsRightKanExtension
      (source_exact_postcompose_counit (A := A) (R := R) (Aprime := Aprime)) := by
  -- TODO: prove this from the canonical scalar-extension right Kan extension by showing that
  -- exact postcomposition with `(restrictAprime).mapDerivedCategory` preserves that specific
  -- right Kan extension.
  sorry

private theorem sourceCounit_isLeftDerivedFunctor
    :
    (((derivedTensorWithAlgebra (algebraMap R Rprime) : DModR ⥤ DModRprime) ⋙
      (restrictAprime).mapDerivedCategory)).IsLeftDerivedFunctor sourceCounit QisR := by
  -- Route correction: instead of unfolding the scalar-change construction, preserve the canonical
  -- right Kan extension for `- ⊗[R]^L R'` across exact restriction and then transport the counit
  -- through `source_postcompose_iso`.
  rw [Functor.isLeftDerivedFunctor_iff_isRightKanExtension]
  -- Transport the right Kan extension witness across the packaging isomorphism for exact
  -- restriction.
  exact
    (Functor.isRightKanExtension_iff_of_iso₂
      (source_exact_postcompose_counit (A := A) (R := R) (Aprime := Aprime))
      (sourceCounit (A := A) (R := R) (Aprime := Aprime))
      (source_postcompose_iso (A := A) (R := R) (Aprime := Aprime))
      (Iso.refl _)
      (by
        simpa using
          (source_exact_postcompose_counit_comp_eq_sourceCounit
            (A := A) (R := R) (Aprime := Aprime)).symm)).1
      (source_exact_postcompose_isRightKanExtension (A := A) (R := R) (Aprime := Aprime))

/-- The target underived functor factors through the localization `Qh_R`, so
`-|_A ⊗_A^L A'` is its left derived functor. -/
private theorem targetCounit_eq_exact_postcompose_counit
    :
    targetCounit (A := A) (R := R) (Aprime := Aprime) =
      (by
        letI :
            Limits.PreservesFiniteLimits (restrictA : ModuleCat R ⥤ ModuleCat A) := by
          infer_instance
        exact
          (Functor.associator
              QhR
              (restrictA).mapDerivedCategory
              (derivedTensorWithAlgebra (algebraMap A Aprime) : DModA ⥤ DModAprime)).hom ≫
            Functor.whiskerRight
              (by
                -- Exact restriction identifies the derived restriction with the homotopy-level one.
                simpa [restrictHot] using
                  (((restrictA).mapDerivedCategoryFactorsh.hom) :
                    QhR ⋙ (restrictA).mapDerivedCategory ⟶
                      restrictHot ⋙ QhA))
              (derivedTensorWithAlgebra (algebraMap A Aprime) : DModA ⥤ DModAprime) ≫
            (Functor.associator
              restrictHot
              QhA
              (derivedTensorWithAlgebra (algebraMap A Aprime) : DModA ⥤ DModAprime)).inv ≫
            Functor.whiskerLeft restrictHot
              (by
                letI :
                    (extendAprimeToDerived : KModA ⥤ DModAprime).HasLeftDerivedFunctor QisA := by
                  simpa [extendAprimeToDerived] using
                    extendScalarsToDerived_hasLeftDerivedFunctor (algebraMap A Aprime)
                -- This is the canonical counit for deriving `extendAprimeHot`.
                simpa [extendAprimeToDerived] using
                  ((extendAprimeToDerived : KModA ⥤ DModAprime).totalLeftDerivedCounit
                    QhA
                    QisA)) ≫
            (Functor.associator restrictHot extendAprimeHot QhAprime).inv) := by
  -- This is just the explicit definition of `targetCounit`.
  rfl

/-- Helper for 15.61.0.1: the explicit module-level pushout base-change component at `M`. -/
private noncomputable def baseChangeModuleIsoComponent
    (M : ModuleCat R) :
    ((extendRprime : ModuleCat R ⥤ ModuleCat Rprime) ⋙
        (restrictAprime : ModuleCat Rprime ⥤ ModuleCat Aprime)).obj M ≅
      ((restrictA : ModuleCat R ⥤ ModuleCat A) ⋙
        (extendAprime : ModuleCat A ⥤ ModuleCat Aprime)).obj M :=
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
  eLeft ≪≫
    (Algebra.IsPushout.cancelBaseChange A Aprime R Rprime (M : Type u)).toModuleIso ≪≫
    eRight.symm

/-- Helper for 15.61.0.1: the tautological restricted-scalars self-equivalence fixes elements
definitionally. -/
private theorem restrictScalarsSelfEquiv_apply
    {S T : Type u} [CommRing S] [CommRing T] [Algebra S T] (t : T) :
    restrictScalarsSelfEquiv S T t = t := rfl

/-- Helper for 15.61.0.1: the inverse tautological restricted-scalars self-equivalence also fixes
elements definitionally. -/
private theorem restrictScalarsSelfEquiv_symm_apply
    {S T : Type u} [CommRing S] [CommRing T] [Algebra S T] (t : T) :
    (restrictScalarsSelfEquiv S T).symm t = t := rfl

/-- Helper for 15.61.0.1: the restricted-scalars copy of the `A'`-unit gives the same standard
pure tensor as the bare `A'`-unit. -/
private theorem restrict_scalars_self_tensor_one_eq
    {M : Type u} [AddCommGroup M] [Module A M] (m : M) :
    ((restrictScalarsSelfEquiv A Aprime (1 : Aprime)) ⊗ₜ[A] m : Aprime ⊗[A] M) =
      ((1 : Aprime) ⊗ₜ[A] m : Aprime ⊗[A] M) := by
  -- The restriction-of-scalars self-equivalence is literally the identity on `Aprime`.
  simp [restrictScalarsSelfEquiv_apply]

/-- Helper for 15.61.0.1: the left `TensorProduct.AlgebraTensorModule.congr` bridge in
`baseChangeModuleIsoComponent` fixes standard pure tensors. -/
private theorem baseChangeModuleIso_left_congr_tmul_tmul
    (M : ModuleCat R) (a : Aprime) (r : R) (m : M) :
    ((TensorProduct.AlgebraTensorModule.congr
        (restrictScalarsSelfEquiv R Rprime)
        (LinearEquiv.refl R (M : Type u))).toModuleIso.hom)
      ((((a : Aprime) ⊗ₜ[A] (r : R)) ⊗ₜ[R] (m : M) :
        (extendRprime : ModuleCat R ⥤ ModuleCat Rprime).obj M)) =
      ((((a : Aprime) ⊗ₜ[A] (r : R)) ⊗ₜ[R] (m : M) :
        ModuleCat.of Rprime ((Aprime ⊗[A] R) ⊗[R] (M : Type u)))) := by
  -- Normalize the `congr` transport on a pure tensor and then use that
  -- `restrictScalarsSelfEquiv` is definitionally the identity on the ring tensor factor.
  simpa [extendRprime, ModuleCat.extendScalars, ModuleCat.ExtendScalars.obj',
    restrictScalarsSelfEquiv_apply] using
    (TensorProduct.AlgebraTensorModule.congr_tmul
      (restrictScalarsSelfEquiv R Rprime)
      (LinearEquiv.refl R (M : Type u))
      (((a : Aprime) ⊗ₜ[A] (r : R)) : Rprime)
      (m : M))

/-- Helper for 15.61.0.1: the right `TensorProduct.AlgebraTensorModule.congr` bridge in
`baseChangeModuleIsoComponent` also fixes standard pure tensors after inverting the bridge. -/
private theorem baseChangeModuleIso_right_restrict_scalars_factor_tmul
    (M : ModuleCat R) (a : Aprime) (m : (restrictA : ModuleCat R ⥤ ModuleCat A).obj M) :
    ((((restrictScalarsSelfEquiv A Aprime).symm a : Aprime) ⊗ₜ[A] (m : M)) :
      (extendAprime : ModuleCat A ⥤ ModuleCat Aprime).obj
        ((restrictA : ModuleCat R ⥤ ModuleCat A).obj M)) =
      (((a : Aprime) ⊗ₜ[A] (m : M)) :
        (extendAprime : ModuleCat A ⥤ ModuleCat Aprime).obj
          ((restrictA : ModuleCat R ⥤ ModuleCat A).obj M)) := by
  -- The inverse restricted-scalars self-equivalence is definitionally the identity on `Aprime`.
  simp [restrictScalarsSelfEquiv_symm_apply]

/-- Helper for 15.61.0.1: the right `TensorProduct.AlgebraTensorModule.congr` bridge in
`baseChangeModuleIsoComponent` also fixes standard pure tensors after inverting the bridge. -/
private theorem baseChangeModuleIso_right_congr_symm_tmul
    (M : ModuleCat R) (a : Aprime) (m : (restrictA : ModuleCat R ⥤ ModuleCat A).obj M) :
    ((TensorProduct.AlgebraTensorModule.congr
        (restrictScalarsSelfEquiv A Aprime)
        (LinearEquiv.refl A ↑((restrictA : ModuleCat R ⥤ ModuleCat A).obj M))).symm.toModuleIso.hom)
      (((a : Aprime) ⊗ₜ[A] (m : (restrictA : ModuleCat R ⥤ ModuleCat A).obj M) :
        ModuleCat.of Aprime (Aprime ⊗[A] ↑((restrictA : ModuleCat R ⥤ ModuleCat A).obj M)))) =
      (((a : Aprime) ⊗ₜ[A] (m : M) :
        (extendAprime : ModuleCat A ⥤ ModuleCat Aprime).obj
          ((restrictA : ModuleCat R ⥤ ModuleCat A).obj M))) := by
  -- Route correction: isolate the inverse `congr` pure-tensor computation first, and only then
  -- rewrite the restricted-scalars copy of `Aprime` back to the plain tensor factor.
  calc
    ((TensorProduct.AlgebraTensorModule.congr
        (restrictScalarsSelfEquiv A Aprime)
        (LinearEquiv.refl A ↑((restrictA : ModuleCat R ⥤ ModuleCat A).obj M))).symm.toModuleIso.hom)
        (((a : Aprime) ⊗ₜ[A] (m : (restrictA : ModuleCat R ⥤ ModuleCat A).obj M) :
          ModuleCat.of Aprime (Aprime ⊗[A] ↑((restrictA : ModuleCat R ⥤ ModuleCat A).obj M)))) =
      ((((restrictScalarsSelfEquiv A Aprime).symm a : Aprime) ⊗ₜ[A] (m : M)) :
        (extendAprime : ModuleCat A ⥤ ModuleCat Aprime).obj
          ((restrictA : ModuleCat R ⥤ ModuleCat A).obj M)) := by
      -- This is the owner computation rule for `TensorProduct.AlgebraTensorModule.congr`.
      simpa [extendAprime, ModuleCat.extendScalars, ModuleCat.ExtendScalars.obj'] using
        (TensorProduct.AlgebraTensorModule.congr_symm_tmul
          (restrictScalarsSelfEquiv A Aprime)
          (LinearEquiv.refl A ↑((restrictA : ModuleCat R ⥤ ModuleCat A).obj M))
          (a : Aprime)
          (m : (restrictA : ModuleCat R ⥤ ModuleCat A).obj M))
    _ = (((a : Aprime) ⊗ₜ[A] (m : M)) :
        (extendAprime : ModuleCat A ⥤ ModuleCat Aprime).obj
          ((restrictA : ModuleCat R ⥤ ModuleCat A).obj M)) :=
      baseChangeModuleIso_right_restrict_scalars_factor_tmul
        (A := A) (R := R) (Aprime := Aprime) M a m

/-- Helper for 15.61.0.1: the raw pushout-cancellation map fixes the standard unit tensor. -/
private theorem pushout_cancelBaseChange_unit_tmul
    {M : Type u} [AddCommGroup M] [Module R M] [Module A M] [IsScalarTower A R M]
    (m : M) :
    (Algebra.IsPushout.cancelBaseChange A Aprime R Rprime M)
        ((((1 : Aprime) ⊗ₜ[A] (1 : R)) ⊗ₜ[R] m : Rprime ⊗[R] M)) =
      ((1 : Aprime) ⊗ₜ[A] m : Aprime ⊗[A] M) := by
  -- This is the owner computation rule for `cancelBaseChange`, after rewriting the tensor-ring
  -- unit as `1 ⊗ 1`.
  simpa [Algebra.TensorProduct.one_def] using
    (Algebra.IsPushout.cancelBaseChange_tmul (R := A) (S := Aprime) (A := R) (B := Rprime)
      (M := M) m)

/-- Helper for 15.61.0.1: the raw generator `((a ⊗ r) ⊗ m)` is the `A'`-scalar multiple of the
unit generator `((1 ⊗ 1) ⊗ (r • m))`. -/
private theorem pushout_cancelBaseChange_middle_tmul_as_smul_unit
    {M : Type u} [AddCommGroup M] [Module R M] [Module A M] [IsScalarTower A R M]
    (a : Aprime) (r : R) (m : M) :
    ((((a : Aprime) ⊗ₜ[A] (r : R)) ⊗ₜ[R] m : Rprime ⊗[R] M)) =
      a • ((((1 : Aprime) ⊗ₜ[A] (1 : R)) ⊗ₜ[R] (r • m : M)) : Rprime ⊗[R] M) := by
  -- First isolate the outer `A'`-scalar on the left tensor factor, then move the middle `R`
  -- factor across the second tensor product to act on `m`.
  calc
    ((((a : Aprime) ⊗ₜ[A] (r : R)) ⊗ₜ[R] m : Rprime ⊗[R] M)) =
        (((a • (((1 : Aprime) ⊗ₜ[A] (r : R)) : Rprime)) ⊗ₜ[R] m) : Rprime ⊗[R] M) := by
      congr 1
      simpa [one_smul] using
        (TensorProduct.smul_tmul' (R := A) (r := a) (m := (1 : Aprime)) (n := (r : R))).symm
    _ = a • ((((1 : Aprime) ⊗ₜ[A] (r : R)) ⊗ₜ[R] m : Rprime ⊗[R] M)) := by
      simpa using
        (TensorProduct.smul_tmul' (R := R) (r := a)
          (m := (((1 : Aprime) ⊗ₜ[A] (r : R)) : Rprime)) (n := m)).symm
    _ = a • ((((1 : Aprime) ⊗ₜ[A] (1 : R)) ⊗ₜ[R] (r • m : M)) : Rprime ⊗[R] M) := by
      congr 1
      calc
        ((((1 : Aprime) ⊗ₜ[A] (r : R)) ⊗ₜ[R] m : Rprime ⊗[R] M)) =
            (((r • (((1 : Aprime) ⊗ₜ[A] (1 : R)) : Rprime)) ⊗ₜ[R] m) : Rprime ⊗[R] M) := by
          -- Rewrite `1 ⊗ r` as the `R`-scalar multiple of `1 ⊗ 1`.
          congr 1
          rw [Algebra.smul_def]
          change ((1 : Aprime) ⊗ₜ[A] (r : R) : Rprime) =
            (((1 : Aprime) ⊗ₜ[A] (r : R)) : Rprime) * (((1 : Aprime) ⊗ₜ[A] (1 : R)) : Rprime)
          rw [Algebra.TensorProduct.tmul_mul_tmul]
          simp
        _ = ((((1 : Aprime) ⊗ₜ[A] (1 : R)) ⊗ₜ[R] (r • m : M)) : Rprime ⊗[R] M) := by
          -- The balancing relation over `R` moves that scalar from the middle tensor factor to
          -- the module element.
          simpa using
            (TensorProduct.smul_tmul (R := R) (r := r)
              (m := (((1 : Aprime) ⊗ₜ[A] (1 : R)) : Rprime)) (n := m))

/-- Helper for 15.61.0.1: the raw pushout-cancellation map sends the generator
`((a ⊗ r) ⊗ m)` to `a ⊗ (r • m)`. -/
private theorem pushout_cancelBaseChange_tmul
    {M : Type u} [AddCommGroup M] [Module R M] [Module A M] [IsScalarTower A R M]
    (a : Aprime) (r : R) (m : M) :
    (Algebra.IsPushout.cancelBaseChange A Aprime R Rprime M)
        ((((a : Aprime) ⊗ₜ[A] (r : R)) ⊗ₜ[R] m : Rprime ⊗[R] M)) =
      ((a : Aprime) ⊗ₜ[A] (r • m) : Aprime ⊗[A] M) := by
  -- Normalize the generator to an `A'`-scalar multiple of the unit tensor, then evaluate the
  -- owner cancellation formula on that unit tensor.
  calc
    (Algebra.IsPushout.cancelBaseChange A Aprime R Rprime M)
        ((((a : Aprime) ⊗ₜ[A] (r : R)) ⊗ₜ[R] m : Rprime ⊗[R] M)) =
      (Algebra.IsPushout.cancelBaseChange A Aprime R Rprime M)
        (a • ((((1 : Aprime) ⊗ₜ[A] (1 : R)) ⊗ₜ[R] (r • m : M)) : Rprime ⊗[R] M)) := by
      rw [pushout_cancelBaseChange_middle_tmul_as_smul_unit (A := A) (R := R) (Aprime := Aprime)]
    _ =
        a • (Algebra.IsPushout.cancelBaseChange A Aprime R Rprime M)
          ((((1 : Aprime) ⊗ₜ[A] (1 : R)) ⊗ₜ[R] (r • m : M)) : Rprime ⊗[R] M) := by
      rw [map_smul]
    _ = a • ((1 : Aprime) ⊗ₜ[A] (r • m) : Aprime ⊗[A] M) := by
      rw [pushout_cancelBaseChange_unit_tmul (A := A) (R := R) (Aprime := Aprime) (r • m)]
    _ = ((a : Aprime) ⊗ₜ[A] (r • m) : Aprime ⊗[A] M) := by
      simpa [one_smul] using
        (TensorProduct.smul_tmul' (R := A) (r := a) (m := (1 : Aprime)) (n := (r • m : M)))

/-- Helper for 15.61.0.1: after unfolding `baseChangeModuleIsoComponent`, the full left bridge
is the identity on the standard generator `((a ⊗ r) ⊗ m)`. -/
private theorem baseChangeModuleIsoComponent_left_bridge_apply
    (M : ModuleCat R) (a : Aprime) (r : R) (m : M) :
    let eLeftRprime :
        (extendRprime).obj M ≅ ModuleCat.of Rprime ((Aprime ⊗[A] R) ⊗[R] (M : Type u)) := by
      simpa [extendRprime, ModuleCat.extendScalars, ModuleCat.ExtendScalars.obj'] using
        (TensorProduct.AlgebraTensorModule.congr
          (restrictScalarsSelfEquiv R Rprime)
          (LinearEquiv.refl R (M : Type u))).toModuleIso
    let eLeft :
        (restrictAprime).obj ((extendRprime).obj M) ≅
          ModuleCat.of Aprime ((Aprime ⊗[A] R) ⊗[R] (M : Type u)) := by
      exact (restrictAprime).mapIso eLeftRprime ≪≫ restrictOfIso
    eLeft.hom
        ((((a : Aprime) ⊗ₜ[A] (r : R)) ⊗ₜ[R] (m : M) :
          ((extendRprime : ModuleCat R ⥤ ModuleCat Rprime) ⋙
            (restrictAprime : ModuleCat Rprime ⥤ ModuleCat Aprime)).obj M)) =
      ((((a : Aprime) ⊗ₜ[A] (r : R)) ⊗ₜ[R] (m : M) :
        ModuleCat.of Aprime ((Aprime ⊗[A] R) ⊗[R] (M : Type u)))) := by
  -- First normalize the inner `congr` bridge on the pure tensor, then drop the final
  -- restriction-of-scalars identification, which is definitionally the identity.
  dsimp
  simpa [restrictOfIso_hom_apply] using
    (baseChangeModuleIso_left_congr_tmul_tmul (A := A) (R := R) (Aprime := Aprime) M a r m)

/-- Helper for 15.61.0.1: after unfolding `baseChangeModuleIsoComponent`, the full right bridge
also fixes the standard generator `a ⊗ x`. -/
private theorem baseChangeModuleIsoComponent_right_bridge_apply
    (M : ModuleCat R) (a : Aprime) (x : (restrictA : ModuleCat R ⥤ ModuleCat A).obj M) :
    let eRight :
        (extendAprime).obj ((restrictA).obj M) ≅
          ModuleCat.of Aprime (Aprime ⊗[A] ↑((restrictA : ModuleCat R ⥤ ModuleCat A).obj M)) := by
      simpa [restrictA, extendAprime, ModuleCat.extendScalars, ModuleCat.ExtendScalars.obj']
        using
          ((TensorProduct.AlgebraTensorModule.congr
            (restrictScalarsSelfEquiv A Aprime)
            (LinearEquiv.refl A ↑((restrictA : ModuleCat R ⥤ ModuleCat A).obj M))).toModuleIso)
    eRight.symm.hom
        (((a : Aprime) ⊗ₜ[A] (x : (restrictA : ModuleCat R ⥤ ModuleCat A).obj M) :
          ModuleCat.of Aprime (Aprime ⊗[A] ↑((restrictA : ModuleCat R ⥤ ModuleCat A).obj M)))) =
      (((a : Aprime) ⊗ₜ[A] (x : M) :
        ((restrictA : ModuleCat R ⥤ ModuleCat A) ⋙
          (extendAprime : ModuleCat A ⥤ ModuleCat Aprime)).obj M)) := by
  -- After expanding the packaged right bridge, only the inverse `congr` pure-tensor formula
  -- remains.
  dsimp
  simpa using
    (baseChangeModuleIso_right_congr_symm_tmul (A := A) (R := R) (Aprime := Aprime) M a x)

/-- Helper for 15.61.0.1: after unfolding `baseChangeModuleIsoComponent`, the full component map
sends the generator `((a ⊗ r) ⊗ m)` to `a ⊗ (r • m)`. -/
private theorem baseChangeModuleIsoComponent_apply_generator_aux
    (M : ModuleCat R) (a : Aprime) (r : R) (m : M) :
    (baseChangeModuleIsoComponent (A := A) (R := R) (Aprime := Aprime) M).hom
        ((((a : Aprime) ⊗ₜ[A] (r : R)) ⊗ₜ[R] (m : M) :
          ((extendRprime : ModuleCat R ⥤ ModuleCat Rprime) ⋙
            (restrictAprime : ModuleCat Rprime ⥤ ModuleCat Aprime)).obj M)) =
      ((a : Aprime) ⊗ₜ[A] ((r • m : M)) :
        ((restrictA : ModuleCat R ⥤ ModuleCat A) ⋙
          (extendAprime : ModuleCat A ⥤ ModuleCat Aprime)).obj M) := by
  -- Expand the defining composite once, collapse the left bridge, evaluate the middle
  -- cancellation on the normalized generator, and then collapse the right bridge back.
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
    exact (restrictAprime).mapIso eLeftRprime ≪≫ restrictOfIso
  let eRight :
      (extendAprime).obj ((restrictA).obj M) ≅
        ModuleCat.of Aprime (Aprime ⊗[A] (M : Type u)) := by
    simpa [restrictA, extendAprime, ModuleCat.extendScalars, ModuleCat.ExtendScalars.obj']
      using
        ((TensorProduct.AlgebraTensorModule.congr
          (restrictScalarsSelfEquiv A Aprime)
          (LinearEquiv.refl A ↑((restrictA).obj M))).toModuleIso)
  change eRight.symm.hom
      ((Algebra.IsPushout.cancelBaseChange A Aprime R Rprime (M : Type u))
        (eLeft.hom
          ((((a : Aprime) ⊗ₜ[A] (r : R)) ⊗ₜ[R] (m : M) :
            ((extendRprime : ModuleCat R ⥤ ModuleCat Rprime) ⋙
              (restrictAprime : ModuleCat Rprime ⥤ ModuleCat Aprime)).obj M)))) =
    ((a : Aprime) ⊗ₜ[A] ((r • m : M)) :
      ((restrictA : ModuleCat R ⥤ ModuleCat A) ⋙
        (extendAprime : ModuleCat A ⥤ ModuleCat Aprime)).obj M)
  have hLeft :
      eLeft.hom
        ((((a : Aprime) ⊗ₜ[A] (r : R)) ⊗ₜ[R] (m : M) :
          ((extendRprime : ModuleCat R ⥤ ModuleCat Rprime) ⋙
            (restrictAprime : ModuleCat Rprime ⥤ ModuleCat Aprime)).obj M)) =
        ((((a : Aprime) ⊗ₜ[A] (r : R)) ⊗ₜ[R] (m : M) :
          ModuleCat.of Aprime ((Aprime ⊗[A] R) ⊗[R] (M : Type u)))) := by
    dsimp [eLeft, eLeftRprime]
    simpa [restrictOfIso_hom_apply] using
      (baseChangeModuleIso_left_congr_tmul_tmul (A := A) (R := R) (Aprime := Aprime) M a r m)
  have hRight :
      eRight.symm.hom
        (((a : Aprime) ⊗ₜ[A] ((r • m : M)) :
          ModuleCat.of Aprime (Aprime ⊗[A] ↑((restrictA : ModuleCat R ⥤ ModuleCat A).obj M)))) =
        ((a : Aprime) ⊗ₜ[A] ((r • m : M)) :
          ((restrictA : ModuleCat R ⥤ ModuleCat A) ⋙
            (extendAprime : ModuleCat A ⥤ ModuleCat Aprime)).obj M) := by
    dsimp [eRight]
    simpa using
      (baseChangeModuleIso_right_congr_symm_tmul
        (A := A) (R := R) (Aprime := Aprime) M a (r • m : M))
  rw [hLeft]
  rw [pushout_cancelBaseChange_tmul (A := A) (R := R) (Aprime := Aprime) a r m]
  exact hRight

/-- Helper for 15.61.0.1: the module-level base-change component sends the standard tensor
generator to the corresponding generator after cancelling the intermediate base change. -/
private theorem baseChangeModuleIsoComponent_hom_one_tmul
    (M : ModuleCat R) (m : M) :
    (baseChangeModuleIsoComponent (A := A) (R := R) (Aprime := Aprime) M).hom
        ((((1 : Aprime) ⊗ₜ[A] (1 : R)) ⊗ₜ[R] (m : M) :
          ((extendRprime : ModuleCat R ⥤ ModuleCat Rprime) ⋙
            (restrictAprime : ModuleCat Rprime ⥤ ModuleCat Aprime)).obj M)) =
      ((1 : Aprime) ⊗ₜ[A] (m : M) :
          ((restrictA : ModuleCat R ⥤ ModuleCat A) ⋙
          (extendAprime : ModuleCat A ⥤ ModuleCat Aprime)).obj M) := by
  -- This is the generator formula specialized to `a = 1` and `r = 1`.
  simpa using
    (baseChangeModuleIsoComponent_apply_generator_aux
      (A := A) (R := R) (Aprime := Aprime) M (1 : Aprime) (1 : R) m)

/-- Helper for 15.61.0.1: the explicit module-level base-change component sends a general
generator `((a ⊗ r) ⊗ m)` to `a ⊗ (r • m)`. -/
private theorem baseChangeModuleIsoComponent_hom_tmul_tmul
    (M : ModuleCat R) (a : Aprime) (r : R) (m : M) :
    (baseChangeModuleIsoComponent (A := A) (R := R) (Aprime := Aprime) M).hom
        ((((a : Aprime) ⊗ₜ[A] (r : R)) ⊗ₜ[R] (m : M) :
          ((extendRprime : ModuleCat R ⥤ ModuleCat Rprime) ⋙
            (restrictAprime : ModuleCat Rprime ⥤ ModuleCat Aprime)).obj M)) =
      ((a : Aprime) ⊗ₜ[A] ((r • m : M)) :
        ((restrictA : ModuleCat R ⥤ ModuleCat A) ⋙
          (extendAprime : ModuleCat A ⥤ ModuleCat Aprime)).obj M) := by
  -- This is exactly the generator computation established above.
  exact
    baseChangeModuleIsoComponent_apply_generator_aux
      (A := A) (R := R) (Aprime := Aprime) M a r m

/-- Helper for 15.61.0.1: the composite "extend to `A' ⊗[A] R`, then restrict to `A'`" sends a
pure tensor generator `((a ⊗ r) ⊗ m)` to the corresponding generator with `m` replaced by `f m`.
-/
private theorem extend_restrict_map_tmul_tmul
    {M N : ModuleCat R} (f : M ⟶ N) (a : Aprime) (r : R) (m : M) :
    ((extendRprime ⋙ restrictAprime).map f)
        ((((a : Aprime) ⊗ₜ[A] (r : R)) ⊗ₜ[R] (m : M)) :
          ((extendRprime : ModuleCat R ⥤ ModuleCat Rprime) ⋙
            (restrictAprime : ModuleCat Rprime ⥤ ModuleCat Aprime)).obj M) =
      ((((a : Aprime) ⊗ₜ[A] (r : R)) ⊗ₜ[R] (f m : N)) :
        ((extendRprime : ModuleCat R ⥤ ModuleCat Rprime) ⋙
          (restrictAprime : ModuleCat Rprime ⥤ ModuleCat Aprime)).obj N) := by
  -- The composite map is the tensor-product map induced by `f`, so it acts pointwise on the
  -- module factor of a pure tensor.
  rfl

/-- Helper for 15.61.0.1: the composite "restrict to `A`, then extend to `A'`" sends a pure
tensor generator `a ⊗ m` to `a ⊗ f m`. -/
private theorem restrict_extend_map_tmul
    {M N : ModuleCat R} (f : M ⟶ N) (a : Aprime) (m : M) :
    ((restrictA ⋙ extendAprime).map f)
        (((a : Aprime) ⊗ₜ[A] (m : M)) :
          ((restrictA : ModuleCat R ⥤ ModuleCat A) ⋙
            (extendAprime : ModuleCat A ⥤ ModuleCat Aprime)).obj M) =
      ((a : Aprime) ⊗ₜ[A] (f m : N) :
        ((restrictA : ModuleCat R ⥤ ModuleCat A) ⋙
          (extendAprime : ModuleCat A ⥤ ModuleCat Aprime)).obj N) := by
  -- The same tensor-product functoriality applies on the target route.
  rfl

/-- Helper for 15.61.0.1: the explicit module-level base-change components are natural in the
underlying `R`-module. -/
private theorem baseChangeModuleIso_naturality
    {M N : ModuleCat R} (f : M ⟶ N) :
    ((extendRprime ⋙ restrictAprime).map f) ≫ (baseChangeModuleIsoComponent (A := A) (R := R)
      (Aprime := Aprime) N).hom =
      (baseChangeModuleIsoComponent (A := A) (R := R) (Aprime := Aprime) M).hom ≫
        ((restrictA ⋙ extendAprime).map f) := by
  -- TODO: finish the tensor-generator induction proving naturality of the explicit base-change
  -- module isomorphism.
  sorry

/-- The exact module-level base-change isomorphism
`(A' ⊗[A] R) ⊗[R] M ≅ A' ⊗[A] M`. -/
private noncomputable def baseChangeModuleIso
    :
    (extendRprime : ModuleCat R ⥤ ModuleCat Rprime) ⋙
        (restrictAprime : ModuleCat Rprime ⥤ ModuleCat Aprime) ≅
      (restrictA : ModuleCat R ⥤ ModuleCat A) ⋙
        (extendAprime : ModuleCat A ⥤ ModuleCat Aprime) :=
  NatIso.ofComponents
    (fun M ↦ baseChangeModuleIsoComponent (A := A) (R := R) (Aprime := Aprime) M)
    (fun f ↦ baseChangeModuleIso_naturality (A := A) (R := R) (Aprime := Aprime) f)

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

/-- Helper for 15.61.0.1: once the source route is known to admit a left derived functor, the
target homotopy-level route does too by transport across the homotopy-level base-change
isomorphism. -/
private theorem targetHot_hasLeftDerivedFunctor :
    Functor.HasLeftDerivedFunctor (targetHot (A := A) (R := R) (Aprime := Aprime)) QisR := by
  let hSource :
      Functor.HasLeftDerivedFunctor (sourceHot (A := A) (R := R) (Aprime := Aprime)) QisR := by
    letI :
        (sourceDerived (A := A) (R := R) (Aprime := Aprime)).IsLeftDerivedFunctor
          (sourceCounit (A := A) (R := R) (Aprime := Aprime))
          QisR :=
      sourceCounit_isLeftDerivedFunctor (A := A) (R := R) (Aprime := Aprime)
    -- The source-side counit already packages `sourceDerived` as a left derived functor of
    -- `sourceHot`.
    -- TODO: supply the explicit `HasLeftDerivedFunctor` witness once the source-side right Kan
    -- extension helper is closed.
    sorry
  -- Transport existence of the left derived functor across the homotopy-level base-change
  -- isomorphism before tackling the explicit comparison counit.
  exact
    (Functor.hasLeftDerivedFunctor_iff_of_iso
      (baseChangeHomotopyIso (A := A) (R := R) (Aprime := Aprime))
      QisR).1 hSource

private theorem targetCounit_isLeftDerivedFunctor
    :
    (((restrictA).mapDerivedCategory ⋙
      (derivedTensorWithAlgebra (algebraMap A Aprime) : DModA ⥤ DModAprime))).IsLeftDerivedFunctor
      targetCounit
      QisR := by
  letI :
      Functor.HasLeftDerivedFunctor (targetHot (A := A) (R := R) (Aprime := Aprime)) QisR :=
    targetHot_hasLeftDerivedFunctor (A := A) (R := R) (Aprime := Aprime)
  -- Route correction: the existence part is now isolated in `targetHot_hasLeftDerivedFunctor`.
  -- TODO: instantiate `Functor.leftDerivedCompComparison` for the exact-precomposition route,
  -- rewrite its factorization using `target_precompose_iso` and
  -- `targetCounit_eq_exact_postcompose_counit`, and then show the resulting comparison upgrades
  -- `targetCounit` to the canonical left-derived counit.
  sorry

attribute [local instance] sourceCounit_isLeftDerivedFunctor targetCounit_isLeftDerivedFunctor

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
