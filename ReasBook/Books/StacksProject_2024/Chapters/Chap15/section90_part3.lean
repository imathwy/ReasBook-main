import Mathlib
import Mathlib.Algebra.Category.FGModuleCat.Basic
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.Algebra.Homology.Monoidal
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.CategoryTheory.Abelian.Ext
import Mathlib.CategoryTheory.CommSq
import Mathlib.CategoryTheory.Monoidal.Internal.Module
import Mathlib.CategoryTheory.Monoidal.Transport
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
import Mathlib.Data.List.TFAE
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.RingTheory.AdicCompletion.Algebra
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.RingHom.FaithfullyFlat

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_15_90_15 (from Chap15) -/
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

/-! ### Proposition_15_90_16 (from Chap15) -/
open CategoryTheory

noncomputable section

universe u v

section

variable {R : Type u} [CommRing R]
variable {S : Type u} [CommRing S] [Algebra R S]
variable {t : ℕ} (f : Fin t → R)
variable [Module.Flat R S]

/- Domain-style sampling for 15.90.16:
- primary domain: formal glueing for module categories and categorical equivalences;
- sampled owner declarations:
  `formalGlueingCan`,
  `formalGlueingH0_leftQuasiInverse_of_flat_of_quotientMap_bijective`,
  `Functor.IsEquivalence`,
  `Functor.asEquivalence`;
- best owner abstraction:
  the source-facing proposition should expose only the equivalence witness for the canonical
  functor `formalGlueingCan S f`, while the inverse functor and the unit/counit isomorphisms stay
  with the canonical owner API `Functor.asEquivalence`;
- primitive data:
  the canonical functor `formalGlueingCan S f` and the quotient-bijectivity hypothesis;
- derived API:
  any quasi-inverse, unit isomorphism, and counit isomorphism are already canonically derived from
  `Functor.IsEquivalence`, so keeping parallel local wrappers would duplicate the owner API.

Source/core/bridge triage:
- `source-facing`: `formalGlueingCan_isEquivalence_of_flat_of_quotientMap_bijective`;
- `core/canonical`: `Functor.IsEquivalence` and `Functor.asEquivalence`;
- `bridge/view`: none needed here beyond the canonical equivalence API. -/

-- Proof sketch: combine Lemma `15.90.12`, which identifies `H^0 ∘ Can` with the identity under
-- the quotient hypothesis, with Lemma `15.90.15`, which identifies the comparison map after
-- localizing at each `fᵢ`, and Lemma `15.90.8`, which lifts the remaining extension class. This
-- yields essential surjectivity of `Can`, while the previous left quasi-inverse statement gives
-- full faithfulness, hence `Can` is an equivalence.
/-- Proposition 15.90.16: assume `φ : R → S` is a flat ring map and let
`I = (f₁, \ldots, fₜ) ⊂ R`. If the induced quotient map `R ⧸ I → S ⧸ IS` is bijective, then the
canonical formal glueing functor
`Can : Mod_R ⥤ Glue(R → S, f₁, \ldots, fₜ)` is an equivalence of categories, where the codomain is
the genuine formal glueing category from Remark `15.90.10`. -/
theorem formalGlueingCan_isEquivalence_of_flat_of_quotientMap_bijective
    (hquot :
      let I : Ideal R := Ideal.span (Set.range f)
      Function.Bijective
        (Ideal.quotientMap (Ideal.map (algebraMap R S) I) (algebraMap R S) Ideal.le_comap_map)) :
    Functor.IsEquivalence (formalGlueingCan S f) := sorry

end

/-! ### Lemma_15_90_17 (from Chap15) -/
open CategoryTheory
open CategoryTheory.Limits
open ModuleCat

noncomputable section

universe u v

section

variable {R : Type u} [CommRing R]
variable {S : Type v} [CommRing S] [Algebra R S]

/- Domain-style sampling:
- primary domain: flat base change and formal glueing for module morphisms in `ModuleCat`;
- inspected same-domain owners:
  `CategoryTheory.CommSq`,
  `ModuleCat.extendScalars`,
  `idealPowerTorsionRestrictedBaseChange_isEquivalence`,
  `formalGlueingCan`,
  `formalGlueingCan_isEquivalence_of_flat_of_quotientMap_bijective`;
- best owner abstraction: the ambient owner is the canonical base-change functor
  `ModuleCat.extendScalars (algebraMap R S)`, while the comparison compatibilities themselves are
  canonically owned by `CategoryTheory.CommSq`; the source-facing content here is only the
  existence of a descended map together with its comparison isomorphism;
- primitive data: a descended `R`-module, the descended morphism, and the comparison
  isomorphism after extension of scalars;
- derived API: the kernel and cokernel comparison isomorphisms, which come from the flat formal
  glueing equivalence and should stay theorem-level output rather than primitive packaged fields.

Source/core/bridge triage:
- `source-facing`: the two existence statements below;
- `core/canonical`: `ModuleCat.extendScalars (algebraMap R S)` and the formal glueing equivalence;
- `bridge/view`: the comparison isomorphism identifying the given `S`-linear map with the base
  change of the descended `R`-linear map.
-/

-- Proof sketch: choose generators `f₁, ..., fₜ` of `I`, regard the localizations of `φ` as an
-- object of the formal glueing category from Remark `15.90.10`, and apply Proposition `15.90.16`
-- to descend `M'` and the localized comparison data to an `R`-module `M`. The induced morphism in
-- the glueing category then comes from a unique `R`-linear map `M ⟶ N`, and Lemma `15.90.3`
-- gives the kernel and cokernel comparison isomorphisms as derived consequences of the chosen
-- descent datum.
/-- Lemma 15.90.17 (1): let `φ : R → S` be a flat ring map, let `I ⊆ R` be a finitely generated
ideal such that `R ⧸ I → S ⧸ IS` is bijective, and let `M' ⟶ S ⊗[R] N` be an `S`-linear map
whose kernel and cokernel are `IS`-power torsion. Then this map descends to an `R`-linear map
`M ⟶ N` together with an isomorphism `S ⊗[R] M ≅ M'`; the kernel and cokernel comparisons after
base change are derived in the companion theorems below. -/
theorem exists_mapToBaseChangeDescent_of_kernel_cokernel_idealPowerTorsion
    (I : Ideal R) (hflat : (algebraMap R S).Flat) (hI : I.FG)
    (hquot :
      Function.Bijective
        (Ideal.quotientMap
          (Ideal.map (algebraMap R S) I)
          (algebraMap R S)
          Ideal.le_comap_map))
    (N : ModuleCat R) (M' : ModuleCat S)
    (φ : M' ⟶ (extendScalars (algebraMap R S)).obj N)
    (hker : Module.IsIdealPowerTorsion (Ideal.map (algebraMap R S) I) (kernel φ : ModuleCat S))
    (hcoker :
      Module.IsIdealPowerTorsion (Ideal.map (algebraMap R S) I) (cokernel φ : ModuleCat S)) :
    ∃ (M : ModuleCat R) (f : M ⟶ N)
      (e : (extendScalars (algebraMap R S)).obj M ≅ M'),
      CommSq e.hom ((extendScalars (algebraMap R S)).map f) φ (𝟙 _) := sorry

/-- Companion to Lemma 15.90.17 (1): once a descent datum `M, f, e` is chosen, the kernel
comparison after base change is canonical. -/
theorem mapToBaseChangeDescent_kernelIso_of_kernel_idealPowerTorsion
    (I : Ideal R) (hflat : (algebraMap R S).Flat) (hI : I.FG)
    (hquot :
      Function.Bijective
        (Ideal.quotientMap
          (Ideal.map (algebraMap R S) I)
          (algebraMap R S)
          Ideal.le_comap_map))
    (N : ModuleCat R) (M' : ModuleCat S)
    (φ : M' ⟶ (extendScalars (algebraMap R S)).obj N)
    (hker : Module.IsIdealPowerTorsion (Ideal.map (algebraMap R S) I) (kernel φ : ModuleCat S))
    {M : ModuleCat R} (f : M ⟶ N)
    (e : (extendScalars (algebraMap R S)).obj M ≅ M')
    (he : CommSq e.hom ((extendScalars (algebraMap R S)).map f) φ (𝟙 _)) :
    ∃ eker : (extendScalars (algebraMap R S)).obj (kernel f) ≅ kernel φ,
      CommSq
        ((extendScalars (algebraMap R S)).map (kernel.ι f))
        eker.hom
        e.hom
        (kernel.ι φ) := sorry

/-- Companion to Lemma 15.90.17 (1): once a descent datum `M, f, e` is chosen, the cokernel
comparison after base change is canonical. -/
theorem mapToBaseChangeDescent_cokernelIso_of_cokernel_idealPowerTorsion
    (I : Ideal R) (hflat : (algebraMap R S).Flat) (hI : I.FG)
    (hquot :
      Function.Bijective
        (Ideal.quotientMap
          (Ideal.map (algebraMap R S) I)
          (algebraMap R S)
          Ideal.le_comap_map))
    (N : ModuleCat R) (M' : ModuleCat S)
    (φ : M' ⟶ (extendScalars (algebraMap R S)).obj N)
    (hcoker :
      Module.IsIdealPowerTorsion (Ideal.map (algebraMap R S) I) (cokernel φ : ModuleCat S))
    {M : ModuleCat R} (f : M ⟶ N)
    (e : (extendScalars (algebraMap R S)).obj M ≅ M')
    (he : CommSq e.hom ((extendScalars (algebraMap R S)).map f) φ (𝟙 _)) :
    ∃ ecoker : (extendScalars (algebraMap R S)).obj (cokernel f) ≅ cokernel φ,
      CommSq
        ((extendScalars (algebraMap R S)).map (cokernel.π f))
        (𝟙 _)
        ecoker.hom
        (cokernel.π φ) := sorry

-- Proof sketch: localize the map `S ⊗[R] M ⟶ N'` at generators of `I`; each localization is an
-- isomorphism because the kernel and cokernel are `IS`-power torsion. Using the same formal
-- glueing equivalence as in part `(1)`, descend the target `N'` and the localized comparison maps
-- to an `R`-module `N`, and obtain the descended map `M ⟶ N`. Lemma `15.90.3` then identifies the
-- base-changed kernels and cokernels from the chosen descent datum.
/-- Lemma 15.90.17 (2): under the same hypotheses on `R → S` and `I`, let `S ⊗[R] M ⟶ N'` be an
`S`-linear map whose kernel and cokernel are `IS`-power torsion. Then this map descends to an
`R`-linear map `M ⟶ N` together with an isomorphism `S ⊗[R] N ≅ N'`; the kernel and cokernel
comparisons after base change are derived in the companion theorems below. -/
theorem exists_mapFromBaseChangeDescent_of_kernel_cokernel_idealPowerTorsion
    (I : Ideal R) (hflat : (algebraMap R S).Flat) (hI : I.FG)
    (hquot :
      Function.Bijective
        (Ideal.quotientMap
          (Ideal.map (algebraMap R S) I)
          (algebraMap R S)
          Ideal.le_comap_map))
    (M : ModuleCat R) (N' : ModuleCat S)
    (φ : (extendScalars (algebraMap R S)).obj M ⟶ N')
    (hker : Module.IsIdealPowerTorsion (Ideal.map (algebraMap R S) I) (kernel φ : ModuleCat S))
    (hcoker :
      Module.IsIdealPowerTorsion (Ideal.map (algebraMap R S) I) (cokernel φ : ModuleCat S)) :
    ∃ (N : ModuleCat R) (f : M ⟶ N)
      (e : (extendScalars (algebraMap R S)).obj N ≅ N'),
      CommSq ((extendScalars (algebraMap R S)).map f) φ e.hom (𝟙 _) := sorry

/-- Companion to Lemma 15.90.17 (2): once a descent datum `N, f, e` is chosen, the kernel
comparison after base change is canonical. -/
theorem mapFromBaseChangeDescent_kernelIso_of_kernel_idealPowerTorsion
    (I : Ideal R) (hflat : (algebraMap R S).Flat) (hI : I.FG)
    (hquot :
      Function.Bijective
        (Ideal.quotientMap
          (Ideal.map (algebraMap R S) I)
          (algebraMap R S)
          Ideal.le_comap_map))
    (M : ModuleCat R) (N' : ModuleCat S)
    (φ : (extendScalars (algebraMap R S)).obj M ⟶ N')
    (hker : Module.IsIdealPowerTorsion (Ideal.map (algebraMap R S) I) (kernel φ : ModuleCat S))
    {N : ModuleCat R} (f : M ⟶ N)
    (e : (extendScalars (algebraMap R S)).obj N ≅ N')
    (he : CommSq ((extendScalars (algebraMap R S)).map f) φ e.hom (𝟙 _)) :
    ∃ eker : (extendScalars (algebraMap R S)).obj (kernel f) ≅ kernel φ,
      CommSq
        ((extendScalars (algebraMap R S)).map (kernel.ι f))
        eker.hom
        (𝟙 _)
        (kernel.ι φ) := sorry

/-- Companion to Lemma 15.90.17 (2): once a descent datum `N, f, e` is chosen, the cokernel
comparison after base change is canonical. -/
theorem mapFromBaseChangeDescent_cokernelIso_of_cokernel_idealPowerTorsion
    (I : Ideal R) (hflat : (algebraMap R S).Flat) (hI : I.FG)
    (hquot :
      Function.Bijective
        (Ideal.quotientMap
          (Ideal.map (algebraMap R S) I)
          (algebraMap R S)
          Ideal.le_comap_map))
    (M : ModuleCat R) (N' : ModuleCat S)
    (φ : (extendScalars (algebraMap R S)).obj M ⟶ N')
    (hcoker :
      Module.IsIdealPowerTorsion (Ideal.map (algebraMap R S) I) (cokernel φ : ModuleCat S))
    {N : ModuleCat R} (f : M ⟶ N)
    (e : (extendScalars (algebraMap R S)).obj N ≅ N')
    (he : CommSq ((extendScalars (algebraMap R S)).map f) φ e.hom (𝟙 _)) :
    ∃ ecoker : (extendScalars (algebraMap R S)).obj (cokernel f) ≅ cokernel φ,
      CommSq
        ((extendScalars (algebraMap R S)).map (cokernel.π f))
        e.hom
        ecoker.hom
        (cokernel.π φ) := sorry

end

/-! ### Theorem_15_90_18 (from Chap15) -/
open CategoryTheory
open CategoryTheory.Limits

noncomputable section

universe u

section

variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]

/- Domain-style sampling for Theorem 15.90.18:
- primary domain: single-element formal glueing for module categories, expressed as a categorical
  pullback over the localization square `R → S`, `R_f → S_f`;
- sampled owner declarations:
  `Localization.awayMap`,
  `CategoricalPullback.CatCommSqOver`,
  `CategoricalPullback.CatCommSqOver.toFunctorToCategoricalPullback`,
  `formalGlueingCan_isEquivalence_of_flat_of_quotientMap_bijective`;
- best owner abstraction:
  the public source-facing object in this file is the single-element pullback functor
  `formalGlueingSingleFunctor`; the localization map itself is already canonically owned by
  `Localization.awayMap`, while the comparison isomorphism and commutative-square packaging are
  bridge-level implementation data for producing the pullback functor;
- primitive data:
  the ring map `Localization.awayMap (algebraMap R S) f`, the induced commutative square of ring
  homomorphisms, and the two extension-of-scalars functors into `ModuleCat`;
- derived API:
  the pullback functor `formalGlueingSingleFunctor` and the equivalence statement under flatness
  and quotient-bijectivity.

Source/core/bridge triage:
- `source-facing`: `formalGlueingSingleFunctor` and
  `formalGlueingSingleFunctor_isEquivalence_of_flat_of_quotientMap_bijective`;
- `core/canonical`: `Localization.awayMap`, `CatCommSqOver`, and `CategoricalPullback`;
- `bridge/view`: the commutative-square theorem and the internal comparison/square data below.
-/

/-- The commutative square of ring maps underlying the single-element formal glueing functor. -/
-- Proof sketch: both composites are the canonical map `R → S_f`; evaluate on `r : R` and use the
-- defining formula for `Localization.awayMap`.
theorem formalGlueingSingleAwaySquare_commutes (f : R) :
    (algebraMap S (Localization.Away (algebraMap R S f))).comp (algebraMap R S) =
      (Localization.awayMap (algebraMap R S) f).comp
        (algebraMap R (Localization.Away f)) := sorry

/-- The comparison isomorphism between the two ways of extending scalars from `R` to `S_f` in the
single-element formal glueing square. -/
private noncomputable def formalGlueingSingleComparison (f : R) :
    ModuleCat.extendScalars (algebraMap R S) ⋙
        ModuleCat.extendScalars (algebraMap S (Localization.Away (algebraMap R S f))) ≅
      ModuleCat.extendScalars (algebraMap R (Localization.Away f)) ⋙
        ModuleCat.extendScalars (Localization.awayMap (algebraMap R S) f) :=
  (ModuleCat.extendScalarsComp (algebraMap R S)
      (algebraMap S (Localization.Away (algebraMap R S f)))).symm ≪≫
    eqToIso
      (congrArg
        (fun u ↦ ModuleCat.extendScalars u)
        (formalGlueingSingleAwaySquare_commutes f)) ≪≫
    ModuleCat.extendScalarsComp
      (algebraMap R (Localization.Away f))
      (Localization.awayMap (algebraMap R S) f)

/-- The commutative-square datum whose associated categorical-pullback functor is the
single-element formal glueing functor. -/
private noncomputable def formalGlueingSingleSquare (f : R) :
    CategoricalPullback.CatCommSqOver
      (ModuleCat.extendScalars (algebraMap S (Localization.Away (algebraMap R S f))))
      (ModuleCat.extendScalars (Localization.awayMap (algebraMap R S) f))
      (ModuleCat R) where
  fst := ModuleCat.extendScalars (algebraMap R S)
  snd := ModuleCat.extendScalars (algebraMap R (Localization.Away f))
  iso := formalGlueingSingleComparison f

/-- The canonical functor sending an `R`-module `M` to the triple
`(M ⊗[R] S, M_f, can)` in the categorical pullback
`Mod_S ×_{Mod_{S_f}} Mod_{R_f}`. -/
noncomputable abbrev formalGlueingSingleFunctor (S : Type u) [CommRing S] [Algebra R S] (f : R) :
    ModuleCat R ⥤
      CategoricalPullback
        (ModuleCat.extendScalars (algebraMap S (Localization.Away (algebraMap R S f))))
        (ModuleCat.extendScalars (Localization.awayMap (algebraMap R S) f)) :=
  (CategoricalPullback.CatCommSqOver.toFunctorToCategoricalPullback
    (ModuleCat.extendScalars (algebraMap S (Localization.Away (algebraMap R S f))))
    (ModuleCat.extendScalars (Localization.awayMap (algebraMap R S) f))
    (ModuleCat R)).obj
    (formalGlueingSingleSquare f)

-- Proof sketch: identify the target pullback category with the category of triples
-- `(M', M₁, α₁)` from Example `4.31.3`, then specialize Proposition `15.90.16` to the one-element
-- family `f : Fin 1 → R` given by the constant value `f`.
/-- Theorem 15.90.18: if `R → S` is flat and the induced quotient map
`R / fR → S / fS` is bijective, then the canonical functor
`Mod_R ⥤ Mod_S ×_{Mod_{S_f}} Mod_{R_f}` sending `M` to `(M ⊗[R] S, M_f, can)` is an
equivalence. -/
theorem formalGlueingSingleFunctor_isEquivalence_of_flat_of_quotientMap_bijective
    (f : R) [Module.Flat R S]
    (hquot :
      Function.Bijective
        (Ideal.quotientMap
          (Ideal.map (algebraMap R S) (Ideal.span ({f} : Set R)))
          (algebraMap R S)
          Ideal.le_comap_map)) :
    Functor.IsEquivalence (formalGlueingSingleFunctor S f) := sorry

end

/-! ### Proposition_15_90_19 (from Chap15) -/
open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.ObjectProperty

noncomputable section

universe u

namespace FGModuleCat

section CommRing

variable (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]

private noncomputable def restrictScalarsSelfEquiv :
    ↑((ModuleCat.restrictScalars (algebraMap R S)).obj (ModuleCat.of S S)) ≃ₗ[S] S :=
  { __ := AddEquiv.refl S
    map_smul' := fun _ _ ↦ rfl }

private instance restrictScalarsSelfIsScalarTower :
    IsScalarTower R S ↑((ModuleCat.restrictScalars (algebraMap R S)).obj (ModuleCat.of S S)) :=
  IsScalarTower.of_algebraMap_smul fun r s ↦ by
    rfl

private noncomputable def extendScalarsTensorEquiv (M : FGModuleCat R) :
    ↑((ModuleCat.extendScalars (algebraMap R S)).obj M.obj) ≃ₗ[S] TensorProduct R S M.obj :=
  TensorProduct.AlgebraTensorModule.congr
    (restrictScalarsSelfEquiv R S)
    (LinearEquiv.refl R M.obj)

variable {R S}

/-- Extension of scalars on finitely generated modules, obtained by restricting
`ModuleCat.extendScalars` to the canonical owner `FGModuleCat`. -/
noncomputable abbrev extendScalars (f : R →+* S) : FGModuleCat R ⥤ FGModuleCat S :=
  let _ : Algebra R S := f.toAlgebra
  (ModuleCat.isFG S).lift
    ((ModuleCat.isFG R).ι ⋙ ModuleCat.extendScalars f)
    (fun M ↦
      (inferInstance : Module.Finite S (TensorProduct R S M.obj)).equiv
        (by
          simpa using (extendScalarsTensorEquiv R S M)))

omit [Algebra R S] in
@[simp] lemma extendScalars_obj_obj (f : R →+* S) (M : FGModuleCat R) :
    ((extendScalars f).obj M).obj = ((ModuleCat.extendScalars f).obj M.obj) :=
  rfl

omit [Algebra R S] in
@[simp] lemma extendScalars_map_hom (f : R →+* S) {M N : FGModuleCat R} (g : M ⟶ N) :
    ((extendScalars f).map g).hom = (ModuleCat.extendScalars f).map g.hom :=
  rfl

end CommRing

end FGModuleCat

section

variable {R : Type u} [CommRing R] (f : R)

local notation "RHat" => principalAdicCompletion f
local notation "RHatf" => Localization.Away (algebraMap R RHat f)
local notation "Rf" => Localization.Away f
local notation "completionFG" => FGModuleCat.extendScalars (algebraMap R RHat)
local notation "completionOverlapFG" => FGModuleCat.extendScalars (algebraMap RHat RHatf)
local notation "localizationFG" => FGModuleCat.extendScalars (algebraMap R Rf)
local notation "localizationOverlapFG" =>
  FGModuleCat.extendScalars (Localization.awayMap (algebraMap R RHat) f)
local notation "FGGlueCat" =>
  CategoricalPullback
    completionOverlapFG
    localizationOverlapFG

/- Domain-style sampling for 15.90.19:
- primary domain: single-element formal glueing for finitely generated module categories over
  `R`, `R^∧`, `(R^∧)_f`, and `R_f`;
- sampled owner declarations:
  `FGModuleCat`,
  `FGModuleCat.extendScalars`,
  `formalGlueingSingleFunctor`,
  `CategoricalPullback`;
- best owner abstraction:
  the pullback of the finitely generated change-of-rings functors
  `completionOverlapFG` and `localizationOverlapFG`, with
  `formalGlueingSingleFunctor RHat f` used only as the ambient comparison model;
- primitive data:
  the completion ring `RHat`, the localization square
  `R → RHat`, `R → Rf`, `RHat → RHatf`, `Rf → RHatf`, and the canonical owner
  `FGModuleCat.extendScalars` on each edge;
- derived API:
  the formal glueing functor `FGModuleCat R ⥤ FGGlueCat` and the equivalence statement below.

Source/core/bridge triage:
- `source-facing`: `principalAdicFormalGlueingFGFunctor` and
  `principalAdicFormalGlueingFGFunctor_isEquivalence`;
- `core/canonical`: `FGModuleCat`, `FGModuleCat.extendScalars`, and
  `formalGlueingSingleFunctor RHat f`;
- `bridge/view`: the ambient `ModuleCat` formal glueing object used to furnish the comparison
  isomorphism and finiteness witnesses for the pullback object below.
-/

-- Proof sketch: for `M : FGModuleCat R`, the first component of
-- `formalGlueingSingleFunctor RHat f` is extension of scalars
-- `M ⊗[R] R^∧`, and the second component is `M ⊗[R] R_f`. Finite generation is preserved
-- by scalar extension along both `R → R^∧` and `R → R_f`.
/-- The completion component of the single-element formal glueing datum attached to a finitely
generated `R`-module is finitely generated over `R^∧`. -/
theorem principalAdicFormalGlueingSingleFunctor_fst_finite
    (M : FGModuleCat R) :
    Module.Finite RHat (((formalGlueingSingleFunctor RHat f).obj M.obj).fst) := sorry

/-- The localization component of the single-element formal glueing datum attached to a finitely
generated `R`-module is finitely generated over `R_f`. -/
theorem principalAdicFormalGlueingSingleFunctor_snd_finite
    (M : FGModuleCat R) :
    Module.Finite Rf (((formalGlueingSingleFunctor RHat f).obj M.obj).snd) := sorry

/-- The formal glueing functor on finitely generated `R`-modules obtained by restricting the
single-element formal glueing functor for the `f`-adic completion to the pullback
`Mod^{fg}_{R^∧} ×_{Mod^{fg}_{(R^∧)_f}} Mod^{fg}_{R_f}`. -/
noncomputable abbrev principalAdicFormalGlueingFGFunctor :
    FGModuleCat R ⥤ FGGlueCat where
  obj M :=
    let X := (formalGlueingSingleFunctor RHat f).obj M.obj
    CategoricalPullback.mk
      ⟨X.fst, principalAdicFormalGlueingSingleFunctor_fst_finite f M⟩
      ⟨X.snd, principalAdicFormalGlueingSingleFunctor_snd_finite f M⟩
      ((ModuleCat.isFG RHatf).isoMk X.iso)
  map g :=
    let φ := (formalGlueingSingleFunctor RHat f).map g.hom
    CategoricalPullback.Hom.mk
      ((ModuleCat.isFG RHat).homMk φ.fst)
      ((ModuleCat.isFG Rf).homMk φ.snd)
      (by
        apply ObjectProperty.hom_ext
        simpa using φ.w)
  map_id M := by
    ext <;> simp
  map_comp g h := by
    ext <;> simp

-- Proof sketch: the completion map `R → R^∧` is flat for Noetherian `R` by
-- Lemma `10.97.2`, and the quotient map `R / fR → R^∧ / f R^∧` is bijective.
-- Theorem `15.90.18` therefore gives an equivalence for the ambient module categories. The source
-- and target finite-generation conditions are preserved and reflected by the completion and
-- localization functors, so the equivalence restricts to the pullback of the finitely generated
-- module categories.
/-- Proposition 15.90.19: if `R` is Noetherian and `R^∧` is the `f`-adic completion of `R`, then
the functor sending a finitely generated `R`-module `M` to its completion-localization glueing
datum `(M^∧, M_f, can)` defines an equivalence from `Mod^{fg}_R` to the fiber product of the
finitely generated module categories over `R^∧`, `(R^∧)_f`, and `R_f`. -/
theorem principalAdicFormalGlueingFGFunctor_isEquivalence [IsNoetherianRing R] :
    Functor.IsEquivalence (principalAdicFormalGlueingFGFunctor f) := sorry

end

/-! ### Remark_15_90_20 (from Chap15) -/
open CategoryTheory CategoryTheory.Limits ModuleCat
open scoped TensorProduct

noncomputable section

universe u w

private noncomputable abbrev formalGlueingCanEquivalence
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    {t : ℕ} (f : Fin t → R) [Module.Flat R S]
    (hquot :
      let I : Ideal R := Ideal.span (Set.range f)
      Function.Bijective
        (Ideal.quotientMap
          (Ideal.map (algebraMap R S) I)
          (algebraMap R S)
          Ideal.le_comap_map)) :
    ModuleCat R ≌ Glue S f := by
  letI : Functor.IsEquivalence (formalGlueingCan S f) :=
    formalGlueingCan_isEquivalence_of_flat_of_quotientMap_bijective f hquot
  exact (formalGlueingCan S f).asEquivalence

private abbrev FormalGlueingSingleTarget
    (R S : Type u) [CommRing R] [CommRing S] [Algebra R S] (f : R) :=
  Limits.CategoricalPullback
    (ModuleCat.extendScalars (algebraMap S (Localization.Away (algebraMap R S f))))
    (ModuleCat.extendScalars (Localization.awayMap (algebraMap R S) f))

private noncomputable abbrev formalGlueingSingleEquivalence
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    (f : R) [Module.Flat R S]
    (hquot :
      Function.Bijective
        (Ideal.quotientMap
          (Ideal.map (algebraMap R S) (Ideal.span ({f} : Set R)))
          (algebraMap R S)
          Ideal.le_comap_map)) :
    ModuleCat R ≌ FormalGlueingSingleTarget R S f := by
  letI : Functor.IsEquivalence (formalGlueingSingleFunctor S f) :=
    formalGlueingSingleFunctor_isEquivalence_of_flat_of_quotientMap_bijective f hquot
  exact (formalGlueingSingleFunctor S f).asEquivalence

private abbrev PrincipalAdicFGGlueTarget
    (R : Type u) [CommRing R] (f : R) [IsNoetherianRing R] :=
  let RHat := principalAdicCompletion f
  let RHatf := Localization.Away (algebraMap R RHat f)
  Limits.CategoricalPullback
    (FGModuleCat.extendScalars (algebraMap RHat RHatf))
    (FGModuleCat.extendScalars (Localization.awayMap (algebraMap R RHat) f))

private noncomputable abbrev principalAdicFormalGlueingFGEquivalence
    {R : Type u} [CommRing R] (f : R) [IsNoetherianRing R] :
    FGModuleCat R ≌ PrincipalAdicFGGlueTarget R f := by
  letI : Functor.IsEquivalence (principalAdicFormalGlueingFGFunctor f) :=
    principalAdicFormalGlueingFGFunctor_isEquivalence f
  exact (principalAdicFormalGlueingFGFunctor f).asEquivalence

section FormalGlueingEquivalences

variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
variable {t : ℕ} (f : Fin t → R)
variable [Module.Flat R S]
variable
    (hquot :
      let I : Ideal R := Ideal.span (Set.range f)
      Function.Bijective
        (Ideal.quotientMap
          (Ideal.map (algebraMap R S) I)
          (algebraMap R S)
          Ideal.le_comap_map))

/- Domain-style sampling for Remark 15.90.20:
- primary domain: formal glueing equivalences for module categories, together with the monoidal
  structures they transport and the induced tensor-built categories;
- sampled owner declarations:
  `formalGlueingCan_isEquivalence_of_flat_of_quotientMap_bijective`,
  `formalGlueingSingleFunctor_isEquivalence_of_flat_of_quotientMap_bijective`,
  `principalAdicFormalGlueingFGFunctor_isEquivalence`,
  `CategoryTheory.Monoidal.transport`,
  `CategoryTheory.Equivalence.mapMon`,
  `ModuleCat.monModuleEquivalenceAlgebra`;
- best owner abstraction: the three canonical equivalences from Proposition `15.90.16`,
  Theorem `15.90.18`, and Proposition `15.90.19`; the tensor and algebra statements should be
  derived from those equivalences rather than exposed only as four independent objectwise tests;
- primitive data: the formal-glueing functors themselves, together with the flatness and
  quotient-bijectivity hypotheses, or the Noetherian completion hypothesis in the principal-adic
  case;
- derived API: transported monoidal structures on the glueing-side targets, induced equivalences on
  monoid objects, induced algebra equivalences when the source is `ModuleCat`, and the companion
  module-property reflection criteria below.

Source/core/bridge triage:
- `source-facing`: Remark `15.90.20` is about the actual equivalences from `15.90.16/18/19`,
  their preservation of the listed module properties, and their compatibility with tensor
  products;
- `core/canonical`: `Functor.IsEquivalence`, `Functor.asEquivalence`, `Monoidal.transport`,
  `Equivalence.mapMon`, `ModuleCat.monModuleEquivalenceAlgebra`, and the monoidal owner on
  `FGModuleCat`;
- `bridge/view`: the transported monoidal structures on the glueing-side target categories and the
  resulting monoid/algebra comparison functors.
-/

/- Remark 15.90.20, Proposition 15.90.16 monoidal form: direct canonical reuse of the
transported monoidal equivalence attached to the source-facing equivalence from
`formalGlueingCan_isEquivalence_of_flat_of_quotientMap_bijective`. -/
#check (Monoidal.equivalenceTransported (formalGlueingCanEquivalence f hquot) :
  ModuleCat R ≌ Monoidal.Transported (formalGlueingCanEquivalence f hquot))

/- Remark 15.90.20, Proposition 15.90.16 monoid-object form: direct canonical reuse of
`Equivalence.mapMon` applied to the transported formal-glueing equivalence. -/
#check ((Monoidal.equivalenceTransported (formalGlueingCanEquivalence f hquot)).symm.mapMon.symm :
  Mon (ModuleCat R) ≌ Mon (Monoidal.Transported (formalGlueingCanEquivalence f hquot)))

/- Remark 15.90.20, Proposition 15.90.16 algebra form: direct reuse of
`monModuleEquivalenceAlgebra` together with the induced monoid-object equivalence above. -/
#check (monModuleEquivalenceAlgebra.symm.trans
    ((Monoidal.equivalenceTransported (formalGlueingCanEquivalence f hquot)).symm.mapMon.symm) :
  AlgCat R ≌ Mon (Monoidal.Transported (formalGlueingCanEquivalence f hquot)))

end FormalGlueingEquivalences

section SingleFormalGlueingEquivalences

variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
variable [Module.Flat R S]
variable (f : R)
variable
    (hquot :
      Function.Bijective
        (Ideal.quotientMap
          (Ideal.map (algebraMap R S) (Ideal.span ({f} : Set R)))
          (algebraMap R S)
          Ideal.le_comap_map))

/- Remark 15.90.20, Theorem 15.90.18 monoidal form: direct canonical reuse of the transported
monoidal equivalence attached to the single formal-glueing equivalence. -/
#check (Monoidal.equivalenceTransported (formalGlueingSingleEquivalence f hquot) :
  ModuleCat R ≌ Monoidal.Transported (formalGlueingSingleEquivalence f hquot))

/- Remark 15.90.20, Theorem 15.90.18 monoid-object form: direct canonical reuse of
`Equivalence.mapMon` applied to the transported single formal-glueing equivalence. -/
#check ((Monoidal.equivalenceTransported (formalGlueingSingleEquivalence f hquot)).symm.mapMon.symm :
  Mon (ModuleCat R) ≌ Mon (Monoidal.Transported (formalGlueingSingleEquivalence f hquot)))

/- Remark 15.90.20, Theorem 15.90.18 algebra form: direct reuse of
`monModuleEquivalenceAlgebra` together with the induced monoid-object equivalence above. -/
#check (monModuleEquivalenceAlgebra.symm.trans
    ((Monoidal.equivalenceTransported (formalGlueingSingleEquivalence f hquot)).symm.mapMon.symm) :
  AlgCat R ≌ Mon (Monoidal.Transported (formalGlueingSingleEquivalence f hquot)))

end SingleFormalGlueingEquivalences

section PrincipalAdicFormalGlueing

variable {R : Type u} [CommRing R] (f : R) [IsNoetherianRing R]

/- Remark 15.90.20, Proposition 15.90.19 monoidal form: direct canonical reuse of the
transported monoidal equivalence attached to `principalAdicFormalGlueingFGFunctor_isEquivalence`.
-/
#check (Monoidal.equivalenceTransported (principalAdicFormalGlueingFGEquivalence f) :
  FGModuleCat R ≌ Monoidal.Transported (principalAdicFormalGlueingFGEquivalence f))

/- Remark 15.90.20, Proposition 15.90.19 monoid-object form: direct canonical reuse of
`Equivalence.mapMon` applied to the transported finitely generated formal-glueing equivalence. -/
#check ((Monoidal.equivalenceTransported (principalAdicFormalGlueingFGEquivalence f)).symm.mapMon.symm :
  Mon (FGModuleCat R) ≌ Mon (Monoidal.Transported (principalAdicFormalGlueingFGEquivalence f)))

end PrincipalAdicFormalGlueing

section ModulePropertyCriteria

variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
variable {t : ℕ} (f : Fin t → R)
variable [Module.Flat R S]
variable
    (hquot :
      let I : Ideal R := Ideal.span (Set.range f)
      Function.Bijective
        (Ideal.quotientMap
          (Ideal.map (algebraMap R S) I)
          (algebraMap R S)
          Ideal.le_comap_map))

local notation "Away" => LocalizedModule.Away

variable {M : Type w} [AddCommMonoid M] [Module R M]

-- Proof sketch: Proposition `15.90.16` identifies `Mod_R` with the formal glueing category for
-- the data `(R → S, f₁, \ldots, fₜ)`. The cited faithfully flat ascent/descent results for
-- finite generation, finite presentation, flatness, and projectivity then translate each module
-- property on `M` into the same property on the base-change module `S ⊗[R] M` together with all
-- localizations `Away (f i) M`.
/-- Remark 15.90.20, finite case: under the hypotheses of Proposition `15.90.16`, an `R`-module
`M` is finite if and only if its base change `S ⊗[R] M` is finite over `S` and every
localization `Away (f i) M` is finite over `Localization.Away (f i)`. This is the module-property
companion to the owner equivalence and its monoidal consequences above. -/
theorem moduleFinite_iff_finite_tensor_and_localizedAway_of_flat_of_quotientMap_bijective :
    Module.Finite R M ↔
      Module.Finite S (S ⊗[R] M) ∧
        ∀ i : Fin t, Module.Finite (Localization.Away (f i)) (Away (f i) M) := by
  sorry

/-- Remark 15.90.20, finite-presentation case: under the same hypotheses, an `R`-module `M` is
finitely presented if and only if `S ⊗[R] M` is finitely presented over `S` and every
localization `Away (f i) M` is finitely presented over `Localization.Away (f i)`. -/
theorem
    moduleFinitePresentation_iff_finitePresentation_tensor_and_localizedAway_of_flat_of_quotientMap_bijective :
    Module.FinitePresentation R M ↔
      Module.FinitePresentation S (S ⊗[R] M) ∧
        ∀ i : Fin t,
          Module.FinitePresentation (Localization.Away (f i)) (Away (f i) M) := by
  sorry

/-- Remark 15.90.20, flat case: under the same hypotheses, an `R`-module `M` is flat if and only
if `S ⊗[R] M` is flat over `S` and every localization `Away (f i) M` is flat over
`Localization.Away (f i)`. -/
theorem moduleFlat_iff_flat_tensor_and_localizedAway_of_flat_of_quotientMap_bijective :
    Module.Flat R M ↔
      Module.Flat S (S ⊗[R] M) ∧
        ∀ i : Fin t, Module.Flat (Localization.Away (f i)) (Away (f i) M) := by
  sorry

/-- Remark 15.90.20, projective case: under the same hypotheses, an `R`-module `M` is projective
if and only if `S ⊗[R] M` is projective over `S` and every localization `Away (f i) M` is
projective over `Localization.Away (f i)`. -/
theorem moduleProjective_iff_projective_tensor_and_localizedAway_of_flat_of_quotientMap_bijective :
    Module.Projective R M ↔
      Module.Projective S (S ⊗[R] M) ∧
        ∀ i : Fin t, Module.Projective (Localization.Away (f i)) (Away (f i) M) := by
  sorry

end ModulePropertyCriteria

/-! ### Remark_15_90_21 (from Chap15) -/
open CategoryTheory TopCat TopologicalSpace
open TopologicalSpace.Opens

noncomputable section

universe v

section

variable {X : TopCat.{v}}

/-
Domain-style sampling for sheaf gluing on a two-open cover:
- primary domain: sheaf descent along an open cover of a topological space;
- sampled declarations:
  `SheafOpenCoverGlueing`,
  `SheafOpenCoverGlueing.ofSheafFunctor`,
  `sheafRestrictionToOpenCover_isEquivalence`,
  `TopologicalSpace.IsOpenCover.of_sets`;
- owner abstraction: the canonical chapter owner is `SheafOpenCoverGlueing 𝒰`, and the bridge from
  global sheaves to that owner is `SheafOpenCoverGlueing.ofSheafFunctor 𝒰 h𝒰`;
- primitive data: the two opens `U`, `T` and the genuine cover hypothesis `U ⊔ T = ⊤`;
- derived API: the `Bool`-indexed cover attached to `U` and `T`, and the specialization of the
  open-cover equivalence theorem to that cover.

Source/core/bridge triage:
- `source-facing`: the sheaf gluing remark for a cover by two opens;
- `core/canonical`: `SheafOpenCoverGlueing 𝒰`;
- `bridge/view`: the `Bool`-indexed two-open cover used to specialize the canonical equivalence.
-/

/-- The two-member open cover with members `U` and `T`. -/
def twoOpenCover (U T : Opens X) : Bool → Opens X
  | false => U
  | true => T

/-- The family `U, T` is an open cover whenever `U ∪ T = X`. -/
theorem twoOpenCover_isOpenCover {U T : Opens X} (hcover : U ⊔ T = ⊤) :
    IsOpenCover (twoOpenCover U T) := by
  refine IsOpenCover.of_sets (fun b ↦ by
    cases b
    · simpa [twoOpenCover] using U.isOpen
    · simpa [twoOpenCover] using T.isOpen) ?_
  ext x
  constructor
  · intro _
    simp
  · intro _
    have hx : x ∈ (U ⊔ T : Opens X) := by simpa [hcover]
    rcases (show x ∈ U ∨ x ∈ T from by simpa using hx) with hU | hT
    · exact Set.mem_iUnion.2 ⟨false, by simpa [twoOpenCover] using hU⟩
    · exact Set.mem_iUnion.2 ⟨true, by simpa [twoOpenCover] using hT⟩

-- Proof sketch: apply the chapter equivalence theorem for sheaves on an open cover to the
-- `Bool`-indexed family `U, T`.
/-- Remark 15.90.21: if `X = U ∪ T`, then restricting a sheaf on `X` to the two members of the
cover yields the canonical open-cover gluing datum on `U` and `T`, and this restriction functor is
an equivalence. This is the two-open-cover specialization of the chapter's sheaf gluing theorem. -/
theorem sheaf_glueing_along_two_open_cover (U T : Opens X) (hcover : U ⊔ T = ⊤) :
    Functor.IsEquivalence
      (SheafOpenCoverGlueing.ofSheafFunctor
        (twoOpenCover U T) (twoOpenCover_isOpenCover hcover)) := by
  simpa using
    sheafRestrictionToOpenCover_isEquivalence
      (twoOpenCover U T) (twoOpenCover_isOpenCover hcover)

end
