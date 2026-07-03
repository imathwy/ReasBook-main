import Mathlib
import StacksProject_2024.Chap15.«15_6_3_1»
import StacksProject_2024.Chap15.Lemma_15_90_11

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open scoped TensorProduct

universe u v

noncomputable section

section

variable {R : Type u} [CommRing R]
variable (S : Type u) [CommRing S] [Algebra R S]
variable (R' : Type u) [CommRing R'] [Algebra R R']
variable {t : ℕ} (f : Fin t → R)

attribute [local instance] Algebra.TensorProduct.rightAlgebra

local notation "Away" => LocalizedModule.Away
local notation "SBase" => S ⊗[R] R'
local notation "fBase" => fun i ↦ algebraMap R R' (f i)
local notation "GlueBase" => Glue SBase fBase

/-
Domain-style sampling for 15.90.15:
- primary domain: formal-glueing base change for module categories;
- sampled owner declarations:
  `formalGlueingCan`,
  `formalGlueingH0`,
  `moduleCatBaseChangeSquare`,
  `CategoryTheory.conjugateEquiv`;
- best owner abstraction:
  the chapter owner should expose the glueing-side base-change functor itself, together with the
  fixed-vertical `Can` and `H⁰` comparison isomorphisms, just as nearby base-change files expose
  named functors and named comparison squares rather than a bare existential package;
- primitive data:
  the glueing-side base-change functor and the two comparison isomorphisms for `Can` and `H⁰`;
- derived API:
  no extra existential wrapper is needed once those named owners are exposed directly.

Source/core/bridge triage:
- `source-facing`: `formalGlueingBaseChangeFunctor`;
- `core/canonical`: functor composition and natural isomorphism squares, with
  `CatCommSqOver` remaining the generic internal owner;
- `bridge/view`: none beyond the named comparison isomorphisms already exposed below.
-/

-- Proof sketch: build the glueing-side base-change functor by transporting the formal-glueing
-- datum along `R → R'`, and then compare the two composites out of `ModuleCat R` by the canonical
-- extension-of-scalars base-change identifications on the base module and on each localized piece.
-- The `H⁰` comparison is the corresponding right-adjoint mate with respect to the adjunctions of
-- Lemma `15.90.11`.
private noncomputable abbrev formalGlueingAwayBaseAlg (i : Fin t) :
    Localization.Away (f i) →ₐ[R] Localization.Away (fBase i) :=
  Localization.awayMapₐ (Algebra.ofId R R') (f i)

private noncomputable abbrev formalGlueingAwayBaseMap (i : Fin t) :
    Localization.Away (f i) →+* Localization.Away (fBase i) :=
  (formalGlueingAwayBaseAlg R' f i).toRingHom

private instance localizedAwayId_isLocalizedModule
    (a : R) (M : Type v) [AddCommGroup M] [Module (Localization.Away a) M]
    [Module R M] [IsScalarTower R (Localization.Away a) M] :
    IsLocalizedModule.Away a (LinearMap.id : M →ₗ[R] M) := by
  simpa using isLocalizedModule_id (Submonoid.powers a) M (Localization.Away a)

private noncomputable def formalGlueingBaseChangeBase (X : Glue S f) :
    ModuleCat.{max u v} SBase :=
  (ModuleCat.extendScalars (algebraMap S SBase)).obj X.base

private noncomputable def formalGlueingBaseChangeLocal (X : Glue S f) (i : Fin t) :
    ModuleCat.{max u v} (Localization.Away (fBase i)) :=
  (ModuleCat.extendScalars (formalGlueingAwayBaseMap R' f i)).obj (X.glue.localModule i)

private abbrev formalGlueingBaseChangeLocalCarrier (X : Glue S f) (i : Fin t) :=
  ↑(formalGlueingBaseChangeLocal S R' f X i)

private theorem formalGlueingAwayBaseSquare_comm (i : Fin t) :
    (formalGlueingAwayBaseMap R' f i).comp (algebraMap R (Localization.Away (f i))) =
      (algebraMap R' (Localization.Away (fBase i))).comp (algebraMap R R') := by
  sorry

private instance formalGlueingAwayBaseAlgebra (i : Fin t) :
    Algebra (Localization.Away (f i)) (Localization.Away (fBase i)) :=
  (formalGlueingAwayBaseAlg R' f i).toAlgebra

private instance formalGlueingAwayBaseTower (i : Fin t) :
    IsScalarTower R (Localization.Away (f i)) (Localization.Away (fBase i)) :=
  IsScalarTower.of_algebraMap_eq' (formalGlueingAwayBaseSquare_comm R' f i).symm

private instance formalGlueingBaseChangeTensorModule
    (X : Glue S f) (i : Fin t) :
    Module R ((formalGlueingBaseChangeLocal S R' f X i) ⊗[R'] SBase) :=
  Module.restrictScalars R R' ((formalGlueingBaseChangeLocal S R' f X i) ⊗[R'] SBase)

private instance formalGlueingBaseChangeTensorAwayModule
    (X : Glue S f) (i : Fin t) :
    Module (Localization.Away (f i))
      ((formalGlueingBaseChangeLocal S R' f X i) ⊗[R'] SBase) :=
  Module.restrictScalars
    (Localization.Away (f i))
    (Localization.Away (fBase i))
    ((formalGlueingBaseChangeLocal S R' f X i) ⊗[R'] SBase)

private noncomputable def formalGlueingBaseChangeGluedModule (X : Glue S f) :
    ModuleCat.{max u v} R' :=
  (ModuleCat.extendScalars (algebraMap R R')).obj (ModuleCat.of R X.glue.gluedModule)

private noncomputable def formalGlueingBaseChangeCanonicalObj (X : Glue S f) :
    Glue R' fBase :=
  (formalGlueingCan R' fBase).obj (formalGlueingBaseChangeGluedModule S R' f X)

private noncomputable def formalGlueingBaseChangeCanonicalLocalIsoApp
    (X : Glue S f) (i : Fin t) :
    (formalGlueingBaseChangeCanonicalObj S R' f X).glue.localModule i ≅
      formalGlueingBaseChangeLocal S R' f X i :=
  let hcomm :
      (formalGlueingAwayBaseMap R' f i).comp (algebraMap R (Localization.Away (f i))) =
        (algebraMap R' (Localization.Away (fBase i))).comp (algebraMap R R') :=
    formalGlueingAwayBaseSquare_comm R' f i
  (awayExtendScalarsIso (fBase i) (formalGlueingBaseChangeGluedModule S R' f X)).symm ≪≫
    (((moduleCatBaseChangeSquare
        (formalGlueingAwayBaseMap R' f i)
        (algebraMap R' (Localization.Away (fBase i)))
        (algebraMap R (Localization.Away (f i)))
        (algebraMap R R')
        hcomm).iso.app (ModuleCat.of R X.glue.gluedModule)).symm) ≪≫
    (ModuleCat.extendScalars (formalGlueingAwayBaseMap R' f i)).mapIso
      ((awayExtendScalarsIso (f i) (ModuleCat.of R X.glue.gluedModule)) ≪≫
        (X.glue.localizedProjectionLinearEquiv i).toModuleIso)

private noncomputable def formalGlueingBaseChangeCanonicalOverlapIsoApp
    (X : Glue S f) (k : Fin t) (i : Fin t) (j : Fin t) :
    ModuleCat.of (Localization.Away (fBase i * fBase j))
        (Away (fBase i * fBase j) ((formalGlueingBaseChangeCanonicalObj S R' f X).glue.localModule k)) ≅
      ModuleCat.of (Localization.Away (fBase i * fBase j))
        (Away (fBase i * fBase j) (formalGlueingBaseChangeLocal S R' f X k)) :=
  (LinearEquiv.extendScalarsOfIsLocalization
      (Submonoid.powers (fBase i * fBase j))
      (Localization.Away (fBase i * fBase j))
      (awayLocalizeLinearEquiv (fBase i * fBase j)
        ((formalGlueingBaseChangeCanonicalLocalIsoApp S R' f X k).toLinearEquiv.restrictScalars R'))).toModuleIso

private noncomputable def formalGlueingBaseChangeLocalOverlapIso
    (X : Glue S f) (i j : Fin t) :
    ModuleCat.of (Localization.Away (fBase i * fBase j))
        (Away (fBase i * fBase j) (formalGlueingBaseChangeLocal S R' f X i)) ≅
      ModuleCat.of (Localization.Away (fBase i * fBase j))
        (Away (fBase i * fBase j) (formalGlueingBaseChangeLocal S R' f X j)) :=
  (formalGlueingBaseChangeCanonicalOverlapIsoApp S R' f X i i j).symm ≪≫
    (formalGlueingBaseChangeCanonicalObj S R' f X).glue.overlapIso i j ≪≫
    formalGlueingBaseChangeCanonicalOverlapIsoApp S R' f X j i j

private theorem formalGlueingBaseChangeLocalCocycle
    (X : Glue S f) :
    AwayModuleGlueingCocycleCondition fBase
      (formalGlueingBaseChangeLocal S R' f X)
      (formalGlueingBaseChangeLocalOverlapIso S R' f X) := by
  sorry

private noncomputable def formalGlueingBaseChangeGlue (X : Glue S f) :
    AwayModuleGlueing fBase where
  localModule := formalGlueingBaseChangeLocal S R' f X
  overlapIso := formalGlueingBaseChangeLocalOverlapIso S R' f X
  cocycle := formalGlueingBaseChangeLocalCocycle S R' f X

private noncomputable def formalGlueingBaseChangeBaseRestrictIsoApp
    (X : Glue S f) :
    ModuleCat.of R' ↑(formalGlueingBaseChangeBase S R' f X) ≅
      (ModuleCat.extendScalars (algebraMap R R')).obj (ModuleCat.of R X.base) :=
  let eTensor :
      ModuleCat.of R' ↑(formalGlueingBaseChangeBase S R' f X) ≅
        ModuleCat.of R' (SBase ⊗[S] X.base) :=
    ((moduleCatExtendScalarsTensorIso S SBase X.base).toLinearEquiv.restrictScalars R').toModuleIso
  let ePushout :
      ModuleCat.of R' (SBase ⊗[S] X.base) ≅
        ModuleCat.of R' (R' ⊗[R] X.base) :=
    (Algebra.IsPushout.cancelBaseChange R R' S SBase X.base).toModuleIso
  let eBase :
      (ModuleCat.extendScalars (algebraMap R R')).obj (ModuleCat.of R X.base) ≅
        ModuleCat.of R' (R' ⊗[R] X.base) :=
    moduleCatExtendScalarsTensorIso R R' (ModuleCat.of R X.base)
  eTensor ≪≫ ePushout ≪≫ eBase.symm

private noncomputable def formalGlueingBaseChangeBaseLocalIsoApp
    (X : Glue S f) (i : Fin t) :
    ModuleCat.of (Localization.Away (fBase i))
        (Away (fBase i) (formalGlueingBaseChangeBase S R' f X)) ≅
      (ModuleCat.extendScalars (formalGlueingAwayBaseMap R' f i)).obj
        (ModuleCat.of (Localization.Away (f i)) (Away (f i) X.base)) :=
  let hcomm :
      (formalGlueingAwayBaseMap R' f i).comp (algebraMap R (Localization.Away (f i))) =
        (algebraMap R' (Localization.Away (fBase i))).comp (algebraMap R R') :=
    formalGlueingAwayBaseSquare_comm R' f i
  (awayExtendScalarsIso (fBase i)
    (ModuleCat.of R' (formalGlueingBaseChangeBase S R' f X))).symm ≪≫
    (ModuleCat.extendScalars (algebraMap R' (Localization.Away (fBase i)))).mapIso
      (formalGlueingBaseChangeBaseRestrictIsoApp S R' f X) ≪≫
    (((moduleCatBaseChangeSquare
        (formalGlueingAwayBaseMap R' f i)
        (algebraMap R' (Localization.Away (fBase i)))
        (algebraMap R (Localization.Away (f i)))
        (algebraMap R R')
        hcomm).iso.app (ModuleCat.of R X.base)).symm) ≪≫
    (ModuleCat.extendScalars (formalGlueingAwayBaseMap R' f i)).mapIso
      (awayExtendScalarsIso (f i) (ModuleCat.of R X.base))

private noncomputable def formalGlueingBaseChangeLocalUnit
    (X : Glue S f) (i : Fin t) :
    X.glue.localModule i →ₗ[Localization.Away (f i)]
      (ModuleCat.restrictScalars (formalGlueingAwayBaseMap R' f i)).obj
        (formalGlueingBaseChangeLocal S R' f X i) :=
  ((ModuleCat.extendRestrictScalarsAdj (formalGlueingAwayBaseMap R' f i)).unit.app
    (X.glue.localModule i)).hom

private noncomputable def formalGlueingBaseChangeScalarLinearMap :
    S →ₗ[R] SBase :=
  (TensorProduct.mk R S R').flip 1

private noncomputable def formalGlueingBaseChangeComparisonAux₂
    (X : Glue S f) (i : Fin t) :
    X.glue.localModule i →ₗ[R]
      S →ₗ[R]
        (ModuleCat.restrictScalars (formalGlueingAwayBaseMap R' f i)).obj <|
          ModuleCat.of (Localization.Away (fBase i))
            (formalGlueingBaseChangeLocal S R' f X i ⊗[R'] SBase) :=
  { toFun := fun m ↦
      { toFun := fun s ↦
          TensorProduct.tmul
            R'
            ((formalGlueingBaseChangeLocalUnit S R' f X i).restrictScalars R m)
            (TensorProduct.tmul R s 1)
        map_add' := by
          sorry
        map_smul' := by
          sorry }
    map_add' := by
      sorry
    map_smul' := by
      sorry }

private noncomputable def formalGlueingBaseChangeComparisonAux₁
    (X : Glue S f) (i : Fin t) :
    ModuleCat.of (Localization.Away (f i))
      (X.glue.localModule i ⊗[R] S) ⟶
      (ModuleCat.restrictScalars (formalGlueingAwayBaseMap R' f i)).obj <|
        ModuleCat.of (Localization.Away (fBase i))
          (formalGlueingBaseChangeLocal S R' f X i ⊗[R'] SBase) :=
  ModuleCat.ofHom
    { toFun := TensorProduct.lift (formalGlueingBaseChangeComparisonAux₂ S R' f X i)
      map_add' := by
        sorry
      map_smul' := by
        sorry }

private noncomputable def formalGlueingBaseChangeComparisonHomApp
    (X : Glue S f) (i : Fin t) :
    ModuleCat.of (Localization.Away (fBase i))
      (Away (fBase i) (formalGlueingBaseChangeBase S R' f X)) ⟶
      ModuleCat.of (Localization.Away (fBase i))
        (formalGlueingBaseChangeLocal S R' f X i ⊗[R'] SBase) :=
  (formalGlueingBaseChangeBaseLocalIsoApp S R' f X i).hom ≫
    (ModuleCat.extendScalars (formalGlueingAwayBaseMap R' f i)).map (X.comparisonIso i).hom ≫
    ((ModuleCat.extendRestrictScalarsAdj (formalGlueingAwayBaseMap R' f i)).homEquiv
      (ModuleCat.of (Localization.Away (f i)) (X.glue.localModule i ⊗[R] S))
      (ModuleCat.of (Localization.Away (fBase i))
        (formalGlueingBaseChangeLocal S R' f X i ⊗[R'] SBase))
      ).symm (formalGlueingBaseChangeComparisonAux₁ S R' f X i)

private theorem formalGlueingBaseChangeComparisonHomApp_isIso
    (X : Glue S f) (i : Fin t) :
    IsIso (formalGlueingBaseChangeComparisonHomApp S R' f X i) := by
  sorry

private noncomputable def formalGlueingBaseChangeComparisonIsoApp
    (X : Glue S f) (i : Fin t) :
    ModuleCat.of (Localization.Away (fBase i))
        (Away (fBase i) (formalGlueingBaseChangeBase S R' f X)) ≅
      ModuleCat.of (Localization.Away (fBase i))
        ((formalGlueingBaseChangeGlue S R' f X).localModule i ⊗[R'] SBase) := by
  exact
    @CategoryTheory.asIso
      _ _ _ _
      (formalGlueingBaseChangeComparisonHomApp S R' f X i)
      (formalGlueingBaseChangeComparisonHomApp_isIso S R' f X i)

private theorem formalGlueingBaseChangeComparisonOverlap
    (X : Glue S f) (i j : Fin t) :
    CommSq
      (formalGlueingComparisonOnOverlap fBase
        (formalGlueingBaseChangeBase S R' f X)
        (formalGlueingBaseChangeGlue S R' f X)
        (formalGlueingBaseChangeComparisonIsoApp S R' f X) i j)
      (𝟙 _)
      (formalGlueingTensorOverlapMap fBase (formalGlueingBaseChangeGlue S R' f X) i j)
      (formalGlueingComparisonOnOppositeOverlap fBase
        (formalGlueingBaseChangeBase S R' f X)
        (formalGlueingBaseChangeGlue S R' f X)
        (formalGlueingBaseChangeComparisonIsoApp S R' f X) i j) := by
  sorry

private noncomputable def formalGlueingBaseChangeObj (X : Glue S f) :
    GlueBase :=
  { base := formalGlueingBaseChangeBase S R' f X
    glue := formalGlueingBaseChangeGlue S R' f X
    comparisonIso := formalGlueingBaseChangeComparisonIsoApp S R' f X
    comparison_overlap := formalGlueingBaseChangeComparisonOverlap S R' f X }

private theorem formalGlueingBaseChangeMapComparison
    {X Y : Glue S f} (φ : X ⟶ Y) (i : Fin t) :
    CommSq
      (ModuleCat.ofHom
        (LocalizedModule.map (Submonoid.powers (fBase i))
          (((ModuleCat.extendScalars (algebraMap S SBase)).map φ.base).hom.restrictScalars R')))
      (formalGlueingBaseChangeComparisonIsoApp S R' f X i).hom
      (formalGlueingBaseChangeComparisonIsoApp S R' f Y i).hom
      (ModuleCat.ofHom <|
        (LinearMap.extendScalarsOfIsLocalizationEquiv
          (Submonoid.powers (fBase i)) (Localization.Away (fBase i)))
          (TensorProduct.map
            (((ModuleCat.extendScalars (formalGlueingAwayBaseMap R' f i)).map
              (φ.glue.localMap i)).hom.restrictScalars R')
            (LinearMap.id : SBase →ₗ[R'] SBase))) := by
  sorry

private theorem formalGlueingBaseChangeMapOverlapComm
    {X Y : Glue S f} (φ : X ⟶ Y) (i j : Fin t) :
    CommSq
      (ModuleCat.ofHom
        (LocalizedModule.map (Submonoid.powers (fBase i * fBase j))
          (((ModuleCat.extendScalars (formalGlueingAwayBaseMap R' f i)).map
            (φ.glue.localMap i)).hom.restrictScalars R')))
      (formalGlueingBaseChangeLocalOverlapIso S R' f X i j).hom
      (formalGlueingBaseChangeLocalOverlapIso S R' f Y i j).hom
      (ModuleCat.ofHom
        (LocalizedModule.map (Submonoid.powers (fBase i * fBase j))
          (((ModuleCat.extendScalars (formalGlueingAwayBaseMap R' f j)).map
            (φ.glue.localMap j)).hom.restrictScalars R'))) := by
  sorry

private noncomputable def formalGlueingBaseChangeMap
    {X Y : Glue S f} (φ : X ⟶ Y) :
    formalGlueingBaseChangeObj S R' f X ⟶ formalGlueingBaseChangeObj S R' f Y :=
  { base := (ModuleCat.extendScalars (algebraMap S SBase)).map φ.base
    glue :=
      { localMap := fun i ↦
          (ModuleCat.extendScalars (formalGlueingAwayBaseMap R' f i)).map (φ.glue.localMap i)
        overlap_comm := formalGlueingBaseChangeMapOverlapComm S R' f φ }
    comparison_comm := formalGlueingBaseChangeMapComparison S R' f φ }

private theorem formalGlueingBaseChangeFunctor_map_id
    (X : Glue S f) :
    formalGlueingBaseChangeMap S R' f (𝟙 X) = 𝟙 (formalGlueingBaseChangeObj S R' f X) := by
  sorry

private theorem formalGlueingBaseChangeFunctor_map_comp
    {X Y Z : Glue S f} (φ : X ⟶ Y) (ψ : Y ⟶ Z) :
    formalGlueingBaseChangeMap S R' f (φ ≫ ψ) =
      formalGlueingBaseChangeMap S R' f φ ≫ formalGlueingBaseChangeMap S R' f ψ := by
  sorry

/-- Lemma 15.90.15: the canonical glueing-side base-change functor
`Glue(R → S, f₁, \ldots, fₜ) ⥤ Glue(R' → S ⊗[R] R', f₁', \ldots, fₜ')`. -/
noncomputable def formalGlueingBaseChangeFunctor :
    Glue S f ⥤ GlueBase :=
  { obj := formalGlueingBaseChangeObj S R' f
    map := fun φ ↦ formalGlueingBaseChangeMap S R' f φ
    map_id := formalGlueingBaseChangeFunctor_map_id S R' f
    map_comp := formalGlueingBaseChangeFunctor_map_comp S R' f }

private theorem formalGlueingTensorBaseSquare_comm :
    (algebraMap S SBase).comp (algebraMap R S) =
      (algebraMap R' SBase).comp (algebraMap R R') := by
  sorry

private noncomputable def formalGlueingCanBaseChangeBaseIsoApp
    (M : ModuleCat.{max u v} R) :
    ((ModuleCat.extendScalars (algebraMap R R') ⋙ formalGlueingCan SBase fBase).obj M).base ≅
      ((formalGlueingCan S f ⋙ formalGlueingBaseChangeFunctor S R' f).obj M).base :=
  let hcomm :
      (algebraMap S SBase).comp (algebraMap R S) =
        (algebraMap R' SBase).comp (algebraMap R R') :=
    formalGlueingTensorBaseSquare_comm S R'
  ((moduleCatBaseChangeSquare
      (algebraMap S SBase)
      (algebraMap R' SBase)
      (algebraMap R S)
      (algebraMap R R')
      hcomm).iso.app M).symm

private noncomputable def formalGlueingCanBaseChangeLocalIsoApp
    (M : ModuleCat.{max u v} R) (i : Fin t) :
    ((ModuleCat.extendScalars (algebraMap R R') ⋙ formalGlueingCan SBase fBase).obj M).glue.localModule i ≅
      ((formalGlueingCan S f ⋙ formalGlueingBaseChangeFunctor S R' f).obj M).glue.localModule i :=
  let hcomm :
      (formalGlueingAwayBaseMap R' f i).comp (algebraMap R (Localization.Away (f i))) =
        (algebraMap R' (Localization.Away (fBase i))).comp (algebraMap R R') :=
    formalGlueingAwayBaseSquare_comm R' f i
  (awayExtendScalarsIso (fBase i)
      ((ModuleCat.extendScalars (algebraMap R R')).obj M)).symm ≪≫
    (((moduleCatBaseChangeSquare
        (formalGlueingAwayBaseMap R' f i)
        (algebraMap R' (Localization.Away (fBase i)))
        (algebraMap R (Localization.Away (f i)))
        (algebraMap R R')
        hcomm).iso.app M).symm) ≪≫
    (ModuleCat.extendScalars (formalGlueingAwayBaseMap R' f i)).mapIso
      (awayExtendScalarsIso (f i) M)

private noncomputable def formalGlueingCanBaseChangeIsoApp
    (M : ModuleCat.{max u v} R) :
    (ModuleCat.extendScalars (algebraMap R R') ⋙ formalGlueingCan SBase fBase).obj M ≅
      (formalGlueingCan S f ⋙ formalGlueingBaseChangeFunctor S R' f).obj M :=
  { hom :=
      { base := (formalGlueingCanBaseChangeBaseIsoApp S R' f M).hom
        glue :=
          { localMap := fun i ↦ (formalGlueingCanBaseChangeLocalIsoApp S R' f M i).hom
            overlap_comm := by
              intro i j
              sorry }
        comparison_comm := by
          intro i
          sorry }
    inv :=
      { base := (formalGlueingCanBaseChangeBaseIsoApp S R' f M).inv
        glue :=
          { localMap := fun i ↦ (formalGlueingCanBaseChangeLocalIsoApp S R' f M i).inv
            overlap_comm := by
              intro i j
              sorry }
        comparison_comm := by
          intro i
          sorry }
    hom_inv_id := by
      sorry
    inv_hom_id := by
      sorry }

/-- Lemma 15.90.15, `Can`-square form: the canonical formal-glueing functor commutes with base
change up to the indicated fixed-vertical natural isomorphism. -/
noncomputable def formalGlueingCanBaseChangeIso
    :
    ModuleCat.extendScalars (algebraMap R R') ⋙ formalGlueingCan SBase fBase ≅
      formalGlueingCan S f ⋙ formalGlueingBaseChangeFunctor S R' f :=
  NatIso.ofComponents
    (formalGlueingCanBaseChangeIsoApp S R' f)
    (by
      intro M N φ
      sorry)

private noncomputable def formalGlueingH0BaseChangeHomApp
    (X : Glue S f) :
    (formalGlueingH0 S f ⋙ ModuleCat.extendScalars (algebraMap R R')).obj X ⟶
      (formalGlueingBaseChangeFunctor S R' f ⋙ formalGlueingH0 SBase fBase).obj X :=
  let β :
      (formalGlueingCan SBase fBase).obj
          ((ModuleCat.extendScalars (algebraMap R R')).obj ((formalGlueingH0 S f).obj X)) ⟶
        (formalGlueingBaseChangeFunctor S R' f).obj X :=
    (formalGlueingCanBaseChangeIsoApp S R' f ((formalGlueingH0 S f).obj X)).hom ≫
      (formalGlueingBaseChangeFunctor S R' f).map
        ((formalGlueingCanAdjunction f).counit.app X)
  (formalGlueingCanAdjunction fBase).homEquiv _ _ β

private theorem formalGlueingH0BaseChangeHomApp_isIso
    (X : Glue S f) :
    IsIso (formalGlueingH0BaseChangeHomApp S R' f X) := by
  sorry

private noncomputable def formalGlueingH0BaseChangeIsoApp
    (X : Glue S f) :
    (formalGlueingBaseChangeFunctor S R' f ⋙ formalGlueingH0 SBase fBase).obj X ≅
      (formalGlueingH0 S f ⋙ ModuleCat.extendScalars (algebraMap R R')).obj X :=
  letI := formalGlueingH0BaseChangeHomApp_isIso S R' f X
  (asIso (formalGlueingH0BaseChangeHomApp S R' f X)).symm

/-- Lemma 15.90.15, `H⁰`-square form: the degree-zero functor commutes with base change up to the
indicated fixed-vertical natural isomorphism. -/
noncomputable def formalGlueingH0BaseChangeIso
    :
    formalGlueingBaseChangeFunctor S R' f ⋙ formalGlueingH0 SBase fBase ≅
      formalGlueingH0 S f ⋙ ModuleCat.extendScalars (algebraMap R R') :=
  NatIso.ofComponents
    (formalGlueingH0BaseChangeIsoApp S R' f)
    (by
      intro X Y φ
      sorry)

end
