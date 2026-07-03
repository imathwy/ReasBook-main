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


/-! ### Remark_15_90_10 (from Chap15) -/
open CategoryTheory
open scoped TensorProduct

universe u w

noncomputable section

section

variable {R : Type u} [CommRing R]
variable {S : Type u} [CommRing S] [Algebra R S]
variable {t : ℕ}

local notation "Away" => LocalizedModule.Away

private instance moduleCatRestrictScalars (M : ModuleCat.{max u w} S) : Module R M :=
  Module.restrictScalars R S M

private instance moduleCatIsScalarTower (M : ModuleCat.{max u w} S) : IsScalarTower R S M :=
  IsScalarTower.restrictScalars R S M

/-
Domain-style sampling:
- primary domain: formal glueing for module categories over localizations of a finite affine cover;
- sampled owner declarations:
  `AwayModuleGlueing`,
  `CategoryTheory.CommSq`,
  `LocalizedModule.equivTensorProduct`,
  `AwayModuleGlueing.localizedProjectionLinearEquiv`;
- best owner abstraction:
  the base module should live in `ModuleCat S`, and the localized overlap package should reuse the
  chapter-local owner `AwayModuleGlueing f`, with overlap compatibility expressed by the canonical
  square owner `CommSq` rather than by parallel equality-of-composites wrappers;
- primitive data:
  the base `S`-module, the localized module glueing datum, and the comparison isomorphisms;
- derived API:
  the induced overlap comparison morphisms, the category structure on formal glueing data, and the
  canonical functors `Can` and `H^0`.

Source/core/bridge triage:
- `source-facing`: `FormalGlueingDatum`, `FormalGlueingDatum.Hom`, `formalGlueingCan`,
  `formalGlueingH0`;
- `core/canonical`: `ModuleCat`, `AwayModuleGlueing`;
- `bridge/view`: the canonical localization/tensor comparison maps used to express
  compatibility on overlaps.
-/

private abbrev localizedModuleCat
    (a : R) (M : Type w) [AddCommGroup M] [Module R M] :
    ModuleCat.{max u w} R :=
  ModuleCat.of R (Away a M)

private abbrev awayModuleCat
    (a : R) (M : Type w) [AddCommGroup M] [Module R M] :
    ModuleCat.{max u w} (Localization.Away a) :=
  ModuleCat.of (Localization.Away a) (Away a M)

private abbrev awayModuleCatMap
    (a : R) {M N : Type w} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (g : M →ₗ[R] N) :
    awayModuleCat a M ⟶ awayModuleCat a N :=
  ModuleCat.ofHom (LocalizedModule.map (Submonoid.powers a) g)

private abbrev tensorModuleCat
    (R : Type u) [CommRing R] (A : Type u) [CommRing A] [Algebra R A]
    (M : Type w) [AddCommGroup M] [Module R M] :
    ModuleCat.{max u w} R :=
  ModuleCat.of R (A ⊗[R] M)

private noncomputable def restrictScalarsSelfEquiv
    (R : Type u) [CommRing R] (A : Type u) [CommRing A] [Algebra R A] :
    ↑((ModuleCat.restrictScalars (algebraMap R A)).obj (ModuleCat.of A A)) ≃ₗ[A] A :=
  { __ := AddEquiv.refl A
    map_smul' := fun _ _ ↦ rfl }

private instance restrictScalarsSelfIsScalarTower
    (R : Type u) [CommRing R] (A : Type u) [CommRing A] [Algebra R A] :
    IsScalarTower R A ↑((ModuleCat.restrictScalars (algebraMap R A)).obj (ModuleCat.of A A)) :=
  IsScalarTower.of_algebraMap_smul fun r s ↦ by
    rfl

/-- The canonical tensor description of extension of scalars on module categories. -/
noncomputable def moduleCatExtendScalarsTensorIso
    (R : Type u) [CommRing R] (A : Type u) [CommRing A] [Algebra R A]
    (M : Type w) [AddCommGroup M] [Module R M] :
    (ModuleCat.extendScalars (algebraMap R A)).obj (ModuleCat.of R M) ≅
      ModuleCat.of A (A ⊗[R] M) := by
  simpa [ModuleCat.extendScalars, ModuleCat.ExtendScalars.obj'] using
    (TensorProduct.AlgebraTensorModule.congr
      (restrictScalarsSelfEquiv R A)
      (LinearEquiv.refl R M)).toModuleIso

/-- Localization away from `a` is the scalar extension of the module to `Localization.Away a`. -/
noncomputable def awayExtendScalarsIso
    (a : R) (M : ModuleCat.{max u w} R) :
    (ModuleCat.extendScalars (algebraMap R (Localization.Away a))).obj M ≅
      ModuleCat.of (Localization.Away a) (Away a M) :=
  moduleCatExtendScalarsTensorIso R (Localization.Away a) M ≪≫
    ((LocalizedModule.equivTensorProduct (Submonoid.powers a) (↑M)).symm).toModuleIso

private noncomputable abbrev localizedTensorIso
    (R : Type u) [CommRing R] (A : Type u) [CommRing A] [Algebra R A]
    (a : R) (M : Type w) [AddCommGroup M] [Module R M] :
    localizedModuleCat a (A ⊗[R] M) ≅
      tensorModuleCat R A (Away a M) :=
  LinearEquiv.toModuleIso <|
    (LocalizedModule.equivTensorProduct (Submonoid.powers a) (A ⊗[R] M)).restrictScalars R ≪≫ₗ
      (TensorProduct.assoc R (Localization.Away a) A M).symm ≪≫ₗ
      (TensorProduct.congr (TensorProduct.comm R (Localization.Away a) A) (.refl R M)) ≪≫ₗ
      TensorProduct.assoc R A (Localization.Away a) M ≪≫ₗ
      TensorProduct.congr (.refl R A)
        ((LocalizedModule.equivTensorProduct (Submonoid.powers a) M).symm.restrictScalars R)

abbrev localTensorModuleCat
    (A : Type u) [CommRing A] [Algebra R A]
    (a : R) (M : Type w) [AddCommGroup M] [Module (Localization.Away a) M]
    [Module R M] [IsScalarTower R (Localization.Away a) M] :
    ModuleCat.{max u w} (Localization.Away a) :=
  ModuleCat.of (Localization.Away a) (M ⊗[R] A)

private noncomputable abbrev localTensorModuleCatMap
    (A : Type u) [CommRing A] [Algebra R A]
    (a : R) {M N : Type w} [AddCommGroup M] [Module (Localization.Away a) M]
    [Module R M] [IsScalarTower R (Localization.Away a) M]
    [AddCommGroup N] [Module (Localization.Away a) N] [Module R N]
    [IsScalarTower R (Localization.Away a) N] (g : M →ₗ[R] N) :
    localTensorModuleCat A a M ⟶ localTensorModuleCat A a N :=
  ModuleCat.ofHom <|
    (LinearMap.extendScalarsOfIsLocalizationEquiv (Submonoid.powers a) (Localization.Away a))
      (TensorProduct.map g (LinearMap.id : A →ₗ[R] A))

noncomputable abbrev localizedTensorRightIso
    (A : Type u) [CommRing A] [Algebra R A]
    (a : R) (M : Type w) [AddCommGroup M] [Module R M] :
    awayModuleCat a (M ⊗[R] A) ≅ localTensorModuleCat A a (Away a M) :=
  let e :
      Away a (M ⊗[R] A) ≃ₗ[R] Away a M ⊗[R] A :=
    awayLocalizeLinearEquiv a (TensorProduct.comm R M A) ≪≫ₗ
      (localizedTensorIso R A a M).toLinearEquiv ≪≫ₗ
      TensorProduct.comm R A (Away a M)
  (LinearEquiv.extendScalarsOfIsLocalization (Submonoid.powers a) (Localization.Away a) e).toModuleIso

private instance localizedAwayModuleInstance
    (a : R) (M : Type w) [AddCommGroup M] [Module (Localization.Away a) M]
    [Module R M] [IsScalarTower R (Localization.Away a) M] :
    IsLocalizedModule.Away a (LinearMap.id : M →ₗ[R] M) := by
  simpa using
    (isLocalizedModule_id (Submonoid.powers a) M (Localization.Away a))

noncomputable abbrev alreadyLocalizedLinearEquiv
    (a : R) (M : Type w) [AddCommGroup M] [Module (Localization.Away a) M]
    [Module R M] [IsScalarTower R (Localization.Away a) M] :
    Away a M ≃ₗ[R] M :=
  IsLocalizedModule.linearEquiv (Submonoid.powers a)
    (LocalizedModule.mkLinearMap (Submonoid.powers a) M)
    (LinearMap.id : M →ₗ[R] M)

noncomputable abbrev iteratedLocalizedIso
    (a b : R) (M : Type w) [AddCommGroup M] [Module (Localization.Away a) M]
    [Module R M] [IsScalarTower R (Localization.Away a) M] :
    Away b M ≃ₗ[R] Away (a * b) M :=
  let e : M ≃ₗ[R] Away a M := (alreadyLocalizedLinearEquiv a M).symm
  (awayLocalizeLinearEquiv b e).trans (awayMulLinearEquiv a b M)

/-- The canonical comparison between localizing after scalar extension and scalar extension after
localizing away from `a`. -/
noncomputable def awayBaseChangeComparisonIso
    (A : Type u) [CommRing A] [Algebra R A]
    (a : R) (M : ModuleCat.{max u w} R) :
    awayModuleCat a ((ModuleCat.extendScalars (algebraMap R A)).obj M) ≅
      localTensorModuleCat A a (Away a M) :=
  let eBase :
      (↑((ModuleCat.extendScalars (algebraMap R A)).obj M)) ≃ₗ[R] (M ⊗[R] A) :=
    ((moduleCatExtendScalarsTensorIso R A M).toLinearEquiv).restrictScalars R ≪≫ₗ
      TensorProduct.comm R A M
  let e₁ :
      awayModuleCat a ((ModuleCat.extendScalars (algebraMap R A)).obj M) ≅
        awayModuleCat a (M ⊗[R] A) :=
    (LinearEquiv.extendScalarsOfIsLocalization
      (Submonoid.powers a) (Localization.Away a)
      (awayLocalizeLinearEquiv a eBase)).toModuleIso
  e₁ ≪≫ localizedTensorRightIso A a (↑M)

/-- The `i`-th comparison isomorphism localized to the overlap with `j`, expressed in the common
pairwise-localized scalar owner. -/
private noncomputable def formalGlueingComparisonOnOverlapLinearMap
    (f : Fin t → R) (base : ModuleCat.{max u w} S) (glue : AwayModuleGlueing f)
    (comparisonIso :
      ∀ i : Fin t,
        awayModuleCat (f i) base ≅ localTensorModuleCat S (f i) (glue.localModule i))
    (i j : Fin t) :
    Away (f i * f j) base →ₗ[R] (Away (f i * f j) (glue.localModule i) ⊗[R] S) :=
  let eBase :
      Away (f i * f j) base →ₗ[R] Away (f j) (Away (f i) base) :=
    (awayMulLinearEquiv (f i) (f j) base).symm.toLinearMap
  let eComparison :
      Away (f j) (Away (f i) base) →ₗ[R] Away (f j) (glue.localModule i ⊗[R] S) :=
    LocalizedModule.map (Submonoid.powers (f j)) ((comparisonIso i).hom.hom.restrictScalars R)
  let eTensor :
      Away (f j) (glue.localModule i ⊗[R] S) →ₗ[R] (Away (f j) (glue.localModule i) ⊗[R] S) :=
    (localizedTensorRightIso S (f j) (glue.localModule i)).hom.hom
  let eLocal :
      Away (f j) (glue.localModule i) ⊗[R] S →ₗ[R] (Away (f i * f j) (glue.localModule i) ⊗[R] S) :=
    TensorProduct.map (iteratedLocalizedIso (f i) (f j) (glue.localModule i)).toLinearMap
      (LinearMap.id : S →ₗ[R] S)
  eLocal.comp <| eTensor.comp <| eComparison.comp eBase

/-- The `i`-th comparison morphism localized to the overlap with `j`, before applying the overlap
isomorphism on the local side. -/
noncomputable def formalGlueingComparisonOnOverlap
    (f : Fin t → R) (base : ModuleCat.{max u w} S) (glue : AwayModuleGlueing f)
    (comparisonIso :
      ∀ i : Fin t,
        ModuleCat.of (Localization.Away (f i)) (Away (f i) base) ≅
          ModuleCat.of (Localization.Away (f i)) (glue.localModule i ⊗[R] S))
    (i j : Fin t) :
    ModuleCat.of (Localization.Away (f i * f j)) (Away (f i * f j) base) ⟶
      ModuleCat.of (Localization.Away (f i * f j))
        (Away (f i * f j) (glue.localModule i) ⊗[R] S) :=
  ModuleCat.ofHom <|
    (LinearMap.extendScalarsOfIsLocalizationEquiv
      (Submonoid.powers (f i * f j)) (Localization.Away (f i * f j)))
      (formalGlueingComparisonOnOverlapLinearMap f base glue comparisonIso i j)

/-- The local overlap isomorphism tensored up to the `S`-side. -/
noncomputable def formalGlueingTensorOverlapMap
    (f : Fin t → R) (glue : AwayModuleGlueing f) (i j : Fin t) :
    ModuleCat.of (Localization.Away (f i * f j))
        (Away (f i * f j) (glue.localModule i) ⊗[R] S) ⟶
      ModuleCat.of (Localization.Away (f i * f j))
        (Away (f i * f j) (glue.localModule j) ⊗[R] S) :=
  localTensorModuleCatMap S (f i * f j) ((glue.overlapIso i j).hom.hom.restrictScalars R)

/-- The `j`-th overlap comparison, rewritten back to the `(i,j)` overlap. -/
private noncomputable def formalGlueingComparisonOnOppositeOverlapLinearMap
    (f : Fin t → R) (base : ModuleCat.{max u w} S) (glue : AwayModuleGlueing f)
    (comparisonIso :
      ∀ i : Fin t,
        awayModuleCat (f i) base ≅ localTensorModuleCat S (f i) (glue.localModule i))
    (i j : Fin t) :
    Away (f i * f j) base →ₗ[R] (Away (f i * f j) (glue.localModule j) ⊗[R] S) :=
  let eBase :
      Away (f i * f j) base →ₗ[R] Away (f j * f i) base :=
    (awayEqLinearEquiv base (by ring)).toLinearMap
  let eComparison :
      Away (f j * f i) base →ₗ[R] (Away (f j * f i) (glue.localModule j) ⊗[R] S) :=
    formalGlueingComparisonOnOverlapLinearMap f base glue comparisonIso j i
  let eTensor :
      Away (f j * f i) (glue.localModule j) ⊗[R] S →ₗ[R]
        (Away (f i * f j) (glue.localModule j) ⊗[R] S) :=
    TensorProduct.map (awayEqLinearEquiv (glue.localModule j) (by ring)).toLinearMap
      (LinearMap.id : S →ₗ[R] S)
  eTensor.comp <| eComparison.comp eBase

/-- The `j`-th overlap comparison, rewritten back to the `(i,j)` overlap. -/
noncomputable def formalGlueingComparisonOnOppositeOverlap
    (f : Fin t → R) (base : ModuleCat.{max u w} S) (glue : AwayModuleGlueing f)
    (comparisonIso :
      ∀ i : Fin t,
        ModuleCat.of (Localization.Away (f i)) (Away (f i) base) ≅
          ModuleCat.of (Localization.Away (f i)) (glue.localModule i ⊗[R] S))
    (i j : Fin t) :
    ModuleCat.of (Localization.Away (f i * f j)) (Away (f i * f j) base) ⟶
      ModuleCat.of (Localization.Away (f i * f j))
        (Away (f i * f j) (glue.localModule j) ⊗[R] S) :=
  ModuleCat.ofHom <|
    (LinearMap.extendScalarsOfIsLocalizationEquiv
      (Submonoid.powers (f i * f j)) (Localization.Away (f i * f j)))
      (formalGlueingComparisonOnOppositeOverlapLinearMap f base glue comparisonIso i j)

/-- Remark 15.90.10: a formal glueing datum for `R → S` and `f_1, \ldots, f_t` consists of an
`S`-module `M'`, local modules `M_i` over the localizations `R_{f_i}` together with their overlap
glueing data, and comparison isomorphisms `(M')_{f_i} ≅ M_i ⊗_R S`, the owner-friendly exact
canonical equivalent of `S ⊗_R M_i`, whose induced overlap square commutes on pairwise
intersections. -/
structure FormalGlueingDatum (S : Type u) [CommRing S] [Algebra R S] (f : Fin t → R) where
  /-- The base `S`-module `M'`. -/
  base : ModuleCat.{max u w} S
  /-- The localized-side glueing datum `(M_i, α_ij)` over the standard cover `D(f_i)`. -/
  glue : AwayModuleGlueing f
  /-- The comparison isomorphisms `(M')_{f_i} ≅ M_i ⊗_R S`. -/
  comparisonIso :
    ∀ i : Fin t,
      ModuleCat.of (Localization.Away (f i)) (Away (f i) base) ≅
        ModuleCat.of (Localization.Away (f i)) (glue.localModule i ⊗[R] S)
  /-- On pairwise overlaps, the two comparison morphisms form a commutative square. -/
  comparison_overlap :
    ∀ i j : Fin t,
      CommSq
        (formalGlueingComparisonOnOverlap f base glue comparisonIso i j)
        (𝟙 _)
        (formalGlueingTensorOverlapMap f glue i j)
        (formalGlueingComparisonOnOppositeOverlap f base glue comparisonIso i j)

/-- The genuine formal glueing category `Glue(R → S, f₁, \ldots, fₜ)` from Remark `15.90.10`. -/
abbrev Glue (S : Type u) [CommRing S] [Algebra R S] (f : Fin t → R) :=
  FormalGlueingDatum S f

private abbrev formalGlueingBaseMap {f : Fin t → R} {X Y : FormalGlueingDatum S f}
    (i : Fin t) (φ : X.base ⟶ Y.base) :
    awayModuleCat (f i) X.base ⟶ awayModuleCat (f i) Y.base :=
  awayModuleCatMap (f i) (φ.hom.restrictScalars R)

private abbrev formalGlueingTensorMap {f : Fin t → R} {X Y : FormalGlueingDatum S f}
    (i : Fin t) (φ : X.glue.localModule i ⟶ Y.glue.localModule i) :
    localTensorModuleCat S (f i) (X.glue.localModule i) ⟶
      localTensorModuleCat S (f i) (Y.glue.localModule i) :=
  localTensorModuleCatMap S (f i) (φ.hom.restrictScalars R)

@[simp] private theorem formalGlueingBaseMap_id {f : Fin t → R} (X : FormalGlueingDatum S f)
    (i : Fin t) :
    formalGlueingBaseMap i (𝟙 X.base) = 𝟙 _ := by
  sorry

@[simp] private theorem formalGlueingBaseMap_comp {f : Fin t → R}
    {X Y Z : FormalGlueingDatum S f} (i : Fin t) (φ : X.base ⟶ Y.base) (ψ : Y.base ⟶ Z.base) :
    formalGlueingBaseMap i (φ ≫ ψ) = formalGlueingBaseMap i φ ≫ formalGlueingBaseMap i ψ := by
  sorry

@[simp] private theorem formalGlueingTensorMap_id {f : Fin t → R} (X : FormalGlueingDatum S f)
    (i : Fin t) :
    formalGlueingTensorMap i (𝟙 (X.glue.localModule i)) = 𝟙 _ := by
  sorry

@[simp] private theorem formalGlueingTensorMap_comp {f : Fin t → R}
    {X Y Z : FormalGlueingDatum S f} (i : Fin t)
    (φ : X.glue.localModule i ⟶ Y.glue.localModule i)
    (ψ : Y.glue.localModule i ⟶ Z.glue.localModule i) :
    formalGlueingTensorMap i (φ ≫ ψ) = formalGlueingTensorMap i φ ≫ formalGlueingTensorMap i ψ := by
  sorry

namespace FormalGlueingDatum

/-- A morphism of formal glueing data is an `S`-linear map on the base module together with
`R_{f_i}`-linear maps on the localized pieces, compatible with the comparison and overlap
isomorphisms. -/
structure Hom {f : Fin t → R} (X Y : FormalGlueingDatum S f) where
  /-- The map on the base `S`-modules. -/
  base : X.base ⟶ Y.base
  /-- The map on the localized glueing datum, reusing the owner `AwayModuleGlueing.Hom`. -/
  glue : X.glue ⟶ Y.glue
  /-- Compatibility with the comparison isomorphisms `(M')_{f_i} ≅ M_i ⊗_R S`. -/
  comparison_comm :
    ∀ i : Fin t,
      CommSq
        (ModuleCat.ofHom
          (LocalizedModule.map (Submonoid.powers (f i)) (base.hom.restrictScalars R)))
        (X.comparisonIso i).hom
        (Y.comparisonIso i).hom
        (ModuleCat.ofHom <|
          (LinearMap.extendScalarsOfIsLocalizationEquiv
            (Submonoid.powers (f i)) (Localization.Away (f i)))
            (TensorProduct.map ((glue.localMap i).hom.restrictScalars R)
              (LinearMap.id : S →ₗ[R] S)))

@[ext] theorem Hom.ext {f : Fin t → R}
    {X Y : FormalGlueingDatum S f}
    {φ ψ : Hom X Y}
    (hbase : φ.base = ψ.base) (hlocal : ∀ i, φ.glue.localMap i = ψ.glue.localMap i) : φ = ψ := by
  cases φ with
  | mk φbase φglue φcomm =>
      cases ψ with
      | mk ψbase ψglue ψcomm =>
          cases hbase
          have hglue : φglue = ψglue := AwayModuleGlueing.Hom.ext hlocal
          cases hglue
          rfl

namespace Hom

abbrev localMap {f : Fin t → R} {X Y : FormalGlueingDatum S f}
    (φ : Hom X Y) (i : Fin t) :
    X.glue.localModule i ⟶ Y.glue.localModule i :=
  φ.glue.localMap i

theorem overlap_comm {f : Fin t → R} {X Y : FormalGlueingDatum S f}
    (φ : Hom X Y) (i j : Fin t) :
    CommSq
      (ModuleCat.ofHom
        (LocalizedModule.map (Submonoid.powers (f i * f j))
          ((φ.localMap i).hom.restrictScalars R)))
      (X.glue.overlapIso i j).hom
      (Y.glue.overlapIso i j).hom
      (ModuleCat.ofHom
        (LocalizedModule.map (Submonoid.powers (f i * f j))
          ((φ.localMap j).hom.restrictScalars R))) :=
  φ.glue.overlap_comm i j

def id {f : Fin t → R} (X : FormalGlueingDatum S f) : Hom X X :=
  { base := 𝟙 X.base
    glue := 𝟙 X.glue
    comparison_comm := by
      intro i
      refine CommSq.mk ?_
      change formalGlueingBaseMap i (𝟙 X.base) ≫ (X.comparisonIso i).hom =
        (X.comparisonIso i).hom ≫ formalGlueingTensorMap i (𝟙 (X.glue.localModule i))
      simp }

def comp {f : Fin t → R} {X Y Z : FormalGlueingDatum S f}
    (φ : Hom X Y) (ψ : Hom Y Z) :
    Hom X Z :=
  { base := φ.base ≫ ψ.base
    glue := φ.glue ≫ ψ.glue
    comparison_comm := by
      intro i
      change CommSq
        (formalGlueingBaseMap i (φ.base ≫ ψ.base))
        _
        _
        (formalGlueingTensorMap i (φ.localMap i ≫ ψ.localMap i))
      simpa only [formalGlueingBaseMap_comp, formalGlueingTensorMap_comp] using
        CommSq.horiz_comp (φ.comparison_comm i) (ψ.comparison_comm i) }

end Hom
end FormalGlueingDatum

instance {f : Fin t → R} : Category (FormalGlueingDatum S f) where
  Hom X Y := FormalGlueingDatum.Hom X Y
  id := FormalGlueingDatum.Hom.id
  comp := FormalGlueingDatum.Hom.comp
  id_comp := by
    intro X Y φ
    apply FormalGlueingDatum.Hom.ext
    · rfl
    · intro i
      rfl
  comp_id := by
    intro X Y φ
    apply FormalGlueingDatum.Hom.ext
    · rfl
    · intro i
      rfl
  assoc := by
    intro W X Y Z φ ψ χ
    apply FormalGlueingDatum.Hom.ext
    · rfl
    · intro i
      rfl

private theorem localizedAwayId
    (a : R) (M : Type w) [AddCommGroup M] [Module R M] :
    IsLocalizedModule.Away a (LinearMap.id : Away a M →ₗ[R] Away a M) := by
  simpa using
    (isLocalizedModule_id (Submonoid.powers a) (Away a M) (Localization.Away a))

private instance moduleCatAwayModule
    (a : R) (M : ModuleCat.{max u w} (Localization.Away a)) : Module R M :=
  Module.restrictScalars R (Localization.Away a) M

private instance moduleCatAwayIsScalarTower
    (a : R) (M : ModuleCat.{max u w} (Localization.Away a)) :
    IsScalarTower R (Localization.Away a) M :=
  IsScalarTower.restrictScalars R (Localization.Away a) M

noncomputable def formalGlueingCanBaseIso
    (M : ModuleCat.{max u w} R) :
    (ModuleCat.extendScalars (algebraMap R S)).obj M ≅ ModuleCat.of S (S ⊗[R] M) := by
  letI :
      IsScalarTower R S ↑((ModuleCat.restrictScalars (algebraMap R S)).obj (ModuleCat.of S S)) :=
    IsScalarTower.of_algebraMap_smul fun r s ↦ rfl
  let e : ↑((ModuleCat.restrictScalars (algebraMap R S)).obj (ModuleCat.of S S)) ≃ₗ[S] S :=
    { __ := AddEquiv.refl S
      map_smul' := fun _ _ ↦ rfl }
  simpa [ModuleCat.extendScalars, ModuleCat.ExtendScalars.obj'] using
    (TensorProduct.AlgebraTensorModule.congr
      e
      (LinearEquiv.refl R M)).toModuleIso

private noncomputable def formalGlueingCanOverlapLinearEquiv
    (f : Fin t → R) (M : ModuleCat.{max u w} R) (i j : Fin t) :
    Away (f i * f j) (Away (f i) M) ≃ₗ[Localization.Away (f i * f j)]
      Away (f i * f j) (Away (f j) M) := by
  letI : IsLocalizedModule.Away (f i) (LinearMap.id : Away (f i) M →ₗ[R] Away (f i) M) :=
    localizedAwayId (f i) M
  letI : IsLocalizedModule.Away (f j) (LinearMap.id : Away (f j) M →ₗ[R] Away (f j) M) :=
    localizedAwayId (f j) M
  let leftToDirect :
      Away (f i * f j) (Away (f i) M) ≃ₗ[R] Away (f i * f j) M :=
    (iteratedLocalizedIso (f i) (f j) (Away (f i) M)).symm ≪≫ₗ
      awayMulLinearEquiv (f i) (f j) M
  let rightToDirect :
      Away (f i * f j) (Away (f j) M) ≃ₗ[R] Away (f i * f j) M :=
    (awayEqLinearEquiv (Away (f j) M) (mul_comm _ _) ≪≫ₗ
      (iteratedLocalizedIso (f j) (f i) (Away (f j) M)).symm ≪≫ₗ
      awayMulLinearEquiv (f j) (f i) M) ≪≫ₗ
      awayEqLinearEquiv M (mul_comm _ _)
  exact
    (leftToDirect ≪≫ₗ rightToDirect.symm).extendScalarsOfIsLocalization
      (Submonoid.powers (f i * f j)) (Localization.Away (f i * f j))

private noncomputable def formalGlueingCanLocalModule
    (f : Fin t → R) (M : ModuleCat.{max u w} R) (i : Fin t) :
    ModuleCat.{max u w} (Localization.Away (f i)) :=
  ModuleCat.of (Localization.Away (f i)) (Away (f i) M)

private noncomputable def formalGlueingCanLocalLinearEquiv
    (f : Fin t → R) (M : ModuleCat.{max u w} R) (i : Fin t) :
    formalGlueingCanLocalModule f M i ≃ₗ[Localization.Away (f i)] Away (f i) M :=
  LinearEquiv.refl _ _

private noncomputable def formalGlueingCanGlue
    (f : Fin t → R) (M : ModuleCat.{max u w} R) :
    AwayModuleGlueing f where
  localModule := formalGlueingCanLocalModule f M
  overlapIso i j := by
    let e₁Linear :
        Away (f i * f j) (formalGlueingCanLocalModule f M i) ≃ₗ[R]
          Away (f i * f j) (Away (f i) M) :=
      awayLocalizeLinearEquiv (f i * f j) ((formalGlueingCanLocalLinearEquiv f M i).restrictScalars R)
    let e₁ :
        ModuleCat.of (Localization.Away (f i * f j))
            (Away (f i * f j) (formalGlueingCanLocalModule f M i)) ≅
          ModuleCat.of (Localization.Away (f i * f j)) (Away (f i * f j) (Away (f i) M)) :=
      (e₁Linear.extendScalarsOfIsLocalization (Submonoid.powers (f i * f j))
        (Localization.Away (f i * f j))).toModuleIso
    let e₂Linear :
        Away (f i * f j) (formalGlueingCanLocalModule f M j) ≃ₗ[R]
          Away (f i * f j) (Away (f j) M) :=
      awayLocalizeLinearEquiv (f i * f j) ((formalGlueingCanLocalLinearEquiv f M j).restrictScalars R)
    let e₂ :
        ModuleCat.of (Localization.Away (f i * f j))
            (Away (f i * f j) (formalGlueingCanLocalModule f M j)) ≅
          ModuleCat.of (Localization.Away (f i * f j)) (Away (f i * f j) (Away (f j) M)) :=
      (e₂Linear.extendScalarsOfIsLocalization (Submonoid.powers (f i * f j))
        (Localization.Away (f i * f j))).toModuleIso
    exact e₁ ≪≫ (formalGlueingCanOverlapLinearEquiv f M i j).toModuleIso ≪≫ e₂.symm
  cocycle i j k := by
    sorry

@[simp] private theorem formalGlueingCanGlue_localModule
    (f : Fin t → R) (M : ModuleCat.{max u w} R) (i : Fin t) :
    (formalGlueingCanGlue f M).localModule i = formalGlueingCanLocalModule f M i :=
  rfl

private noncomputable def formalGlueingCanGlueLocalLinearEquiv
    (f : Fin t → R) (M : ModuleCat.{max u w} R) (i : Fin t) :
    (formalGlueingCanGlue f M).localModule i ≃ₗ[Localization.Away (f i)] Away (f i) M := by
  simpa [formalGlueingCanGlue_localModule] using
    formalGlueingCanLocalLinearEquiv f M i

private noncomputable def formalGlueingCanObj
    (S : Type u) [CommRing S] [Algebra R S] (f : Fin t → R) (M : ModuleCat.{max u w} R) :
    Glue S f := by
  refine
    { base := (ModuleCat.extendScalars (algebraMap R S)).obj M
      glue := formalGlueingCanGlue f M
      comparisonIso := ?_
      comparison_overlap := ?_ }
  · intro i
    let e :
        localTensorModuleCat S (f i) (Away (f i) M) ≅
          localTensorModuleCat S (f i) ((formalGlueingCanGlue f M).localModule i) :=
      (TensorProduct.AlgebraTensorModule.congr
        (formalGlueingCanGlueLocalLinearEquiv f M i).symm
        (.refl R S)).toModuleIso
    exact awayBaseChangeComparisonIso S (f i) M ≪≫ e
  · intro i j
    sorry

private noncomputable def formalGlueingCanGlueMap
    (f : Fin t → R) {M N : ModuleCat.{max u w} R} (φ : M ⟶ N) :
    formalGlueingCanGlue f M ⟶ formalGlueingCanGlue f N where
  localMap i := by
    change formalGlueingCanLocalModule f M i ⟶ formalGlueingCanLocalModule f N i
    exact ModuleCat.ofHom (LocalizedModule.map (Submonoid.powers (f i)) φ.hom)
  overlap_comm := by
    intro i j
    refine CommSq.mk ?_
    sorry

@[simp] private theorem formalGlueingCanGlueMap_id
    (f : Fin t → R) (M : ModuleCat.{max u w} R) (i : Fin t) :
    (formalGlueingCanGlueMap f (𝟙 M)).localMap i = 𝟙 ((formalGlueingCanGlue f M).localModule i) := by
  change (formalGlueingCanGlueMap f (𝟙 M)).localMap i = 𝟙 (formalGlueingCanLocalModule f M i)
  ext x
  change (LocalizedModule.map (Submonoid.powers (f i)) (LinearMap.id : M →ₗ[R] M)) x = x
  induction x using LocalizedModule.induction_on with
  | _ y s =>
      rw [LocalizedModule.map_mk]
      rfl

@[simp] private theorem formalGlueingCanGlueMap_comp
    (f : Fin t → R) {M N P : ModuleCat.{max u w} R}
    (φ : M ⟶ N) (ψ : N ⟶ P) (i : Fin t) :
    (formalGlueingCanGlueMap f (φ ≫ ψ)).localMap i =
      (formalGlueingCanGlueMap f φ).localMap i ≫ (formalGlueingCanGlueMap f ψ).localMap i := by
  ext x
  change
    (LocalizedModule.map (Submonoid.powers (f i)) (ψ.hom.comp φ.hom)) x =
      ((LocalizedModule.map (Submonoid.powers (f i)) ψ.hom).comp
        (LocalizedModule.map (Submonoid.powers (f i)) φ.hom)) x
  induction x using LocalizedModule.induction_on with
  | _ y s =>
      rw [LinearMap.comp_apply]
      rw [LocalizedModule.map_mk, LocalizedModule.map_mk, LocalizedModule.map_mk]
      rfl

private noncomputable def formalGlueingCanMap
    (S : Type u) [CommRing S] [Algebra R S] (f : Fin t → R)
    {M N : ModuleCat.{max u w} R} (φ : M ⟶ N) :
    formalGlueingCanObj S f M ⟶ formalGlueingCanObj S f N :=
  { base := (ModuleCat.extendScalars (algebraMap R S)).map φ
    glue := formalGlueingCanGlueMap f φ
    comparison_comm := by
      intro i
      refine CommSq.mk ?_
      sorry }

/-- Remark 15.90.10: the canonical functor
`Can : Mod_R ⥤ Glue(R → S, f₁, \ldots, fₜ)`. -/
noncomputable def formalGlueingCan
    (S : Type u) [CommRing S] [Algebra R S]
    (f : Fin t → R) :
    ModuleCat.{max u w} R ⥤ Glue S f :=
  { obj := fun M ↦ formalGlueingCanObj S f M
    map := fun φ ↦ formalGlueingCanMap S f φ
    map_id := by
      intro M
      apply FormalGlueingDatum.Hom.ext
      · change (ModuleCat.extendScalars (algebraMap R S)).map (𝟙 M) = 𝟙 _
        simpa using (ModuleCat.extendScalars (algebraMap R S)).map_id M
      · intro i
        change (formalGlueingCanGlueMap f (𝟙 M)).localMap i =
            𝟙 ((formalGlueingCanGlue f M).localModule i)
        simpa using formalGlueingCanGlueMap_id f M i
    map_comp := by
      intro M N P φ ψ
      apply FormalGlueingDatum.Hom.ext
      · change (ModuleCat.extendScalars (algebraMap R S)).map (φ ≫ ψ) =
            (ModuleCat.extendScalars (algebraMap R S)).map φ ≫
              (ModuleCat.extendScalars (algebraMap R S)).map ψ
        simpa using (ModuleCat.extendScalars (algebraMap R S)).map_comp φ ψ
      · intro i
        change (formalGlueingCanGlueMap f (φ ≫ ψ)).localMap i =
            (formalGlueingCanGlueMap f φ).localMap i ≫
              (formalGlueingCanGlueMap f ψ).localMap i
        simpa using formalGlueingCanGlueMap_comp f φ ψ i }

namespace FormalGlueingDatum

variable {f : Fin t → R}

private abbrev h0Source
    (X : Glue S f) :=
  X.base × X.glue.gluedModule

private abbrev h0ComparisonComponent
    (X : Glue S f) (i : Fin t) :
    h0Source X →ₗ[R] X.glue.localModule i ⊗[R] S :=
  let compare :
      Away (f i) X.base →ₗ[R] X.glue.localModule i ⊗[R] S :=
    (X.comparisonIso i).hom.hom.restrictScalars R
  let localize :
      X.base →ₗ[R] Away (f i) X.base :=
    LocalizedModule.mkLinearMap (Submonoid.powers (f i)) X.base
  (compare.comp localize).comp
      (LinearMap.fst R X.base X.glue.gluedModule)
    -
    ((TensorProduct.mk R (X.glue.localModule i) S).flip 1).comp
      ((X.glue.projection i).comp
        (LinearMap.snd R X.base X.glue.gluedModule))

/-- The degree-zero comparison map attached to a formal glueing datum, with the overlap condition
absorbed into `X.glue.gluedModule`. -/
def h0CompatibilityMap
    (X : Glue S f) :
    (X.base × X.glue.gluedModule) →ₗ[R] (∀ i : Fin t, X.glue.localModule i ⊗[R] S) :=
  LinearMap.pi fun i ↦ h0ComparisonComponent X i

/-- The degree-zero module `H^0(X)` of a formal glueing datum `X`, built from the base
`S`-module and the canonical glued local module. -/
def h0Module
    (X : Glue S f) :
    Submodule R (X.base × X.glue.gluedModule) :=
  LinearMap.ker (h0CompatibilityMap X)

private abbrev h0UnderlyingMap
    {X Y : Glue S f} (φ : X ⟶ Y) :
    h0Source X →ₗ[R] h0Source Y :=
  LinearMap.prodMap
    (φ.base.hom.restrictScalars R)
    φ.glue.gluedMap

private def h0Map
    {X Y : Glue S f} (φ : X ⟶ Y) :
    h0Module X →ₗ[R] h0Module Y :=
  LinearMap.codRestrict
    (h0Module Y)
    (LinearMap.domRestrict
      (h0UnderlyingMap φ)
      (h0Module X))
    (by
      intro x
      sorry)

end FormalGlueingDatum

/-- Remark 15.90.10: the degree-zero functor
`H^0 : Glue(R → S, f₁, \ldots, fₜ) ⥤ Mod_R`. -/
noncomputable def formalGlueingH0
    (S : Type u) [CommRing S] [Algebra R S]
    (f : Fin t → R) :
    Glue S f ⥤ ModuleCat.{max u w} R :=
  { obj := fun X ↦ ModuleCat.of R (X.h0Module)
    map := fun φ ↦ ModuleCat.ofHom (FormalGlueingDatum.h0Map φ)
    map_id := by
      intro X
      sorry
    map_comp := by
      intro X Y Z φ ψ
      sorry }

end

/-! ### Lemma_15_90_11 (from Chap15) -/
open CategoryTheory
open scoped TensorProduct

universe u w

noncomputable section

section

variable {R : Type u} [CommRing R]
variable {S : Type u} [CommRing S] [Algebra R S]
variable {t : ℕ} (f : Fin t → R)

/- Domain-style sampling:
- primary domain: categorical formal glueing for module categories;
- sampled owner declarations:
  `CategoryTheory.Adjunction`,
  `FormalGlueingDatum`,
  `formalGlueingCan`,
  `formalGlueingH0`,
  `Functor.IsLeftAdjoint`;
- best owner abstraction: the source-facing adjunction
  `formalGlueingCan S f ⊣ formalGlueingH0 S f`;
- primitive data: the canonical functors `formalGlueingCan S f` and `formalGlueingH0 S f`;
- derived API: the left/right adjoint typeclass instances used by downstream generic categorical
  lemmas.

Source/core/bridge triage:
- `source-facing`: `formalGlueingCanAdjunction`;
- `core/canonical`: `CategoryTheory.Adjunction`;
- `bridge/view`: the derived adjointness instances below for typeclass-driven reuse.
-/

-- Proof sketch: Remark `15.90.10` already defines the canonical source-facing right adjoint
-- `formalGlueingH0 S f`, so the lemma should expose the actual adjunction
-- `formalGlueingCan S f ⊣ formalGlueingH0 S f`. The proposition-level `IsLeftAdjoint` and
-- `IsRightAdjoint` owners are then derived consequences for downstream typeclass-driven reuse.
/-- Lemma 15.90.11: for the genuine formal glueing category `Glue(R → S, f₁, \ldots, fₜ)` from
Remark `15.90.10`, the canonical functor `Can` is left adjoint to the degree-zero functor
`H^0`. -/
noncomputable def formalGlueingCanAdjunction :
    formalGlueingCan S f ⊣ formalGlueingH0 S f := by
  sorry

noncomputable instance : (formalGlueingCan S f).IsLeftAdjoint :=
  (formalGlueingCanAdjunction f).isLeftAdjoint

noncomputable instance : (formalGlueingH0 S f).IsRightAdjoint :=
  (formalGlueingCanAdjunction f).isRightAdjoint

end

/-! ### Lemma_15_90_12 (from Chap15) -/
open CategoryTheory

noncomputable section

universe u

section

variable {R : Type u} [CommRing R]
variable {S : Type u} [CommRing S] [Algebra R S]
variable {t : ℕ} (f : Fin t → R)

/-
Domain-style sampling:
- primary domain: formal glueing for module categories, with the degree-zero module recovered from
  the canonical formal glueing short complex;
- sampled owner declarations:
  `formalGlueingCan`,
  `formalGlueingH0`,
  `formalGlueingModuleComplex`,
  `ShortComplex.Exact.moduleCat_range_eq_ker`;
- best owner abstraction:
  the source-facing functors `formalGlueingCan` and `formalGlueingH0`, bridged through the owner
  kernel object `LinearMap.ker (formalGlueingModuleComplexBeta S f M)` attached to the formal
  glueing complex;
- primitive data:
  the module `M`, the canonical map `formalGlueingModuleComplexAlpha S f M`, and the kernel-level
  comparison between `H⁰(Can(M))` and `ker β`;
- derived API:
  the componentwise linear equivalence and the resulting natural isomorphism
  `formalGlueingCan S f ⋙ formalGlueingH0 S f ≅ 𝟭`.

Source/core/bridge triage:
- `source-facing`: the natural isomorphism below;
- `core/canonical`: `formalGlueingCan`, `formalGlueingH0`, and
  `ShortComplex.Exact.moduleCat_range_eq_ker`;
- `bridge/view`: the kernel-level comparison between `H⁰(Can(M))` and
  `LinearMap.ker (formalGlueingModuleComplexBeta S f M)`.
-/

private noncomputable def formalGlueingAlphaToKerBeta
    (M : ModuleCat R) :
    M →ₗ[R] LinearMap.ker (formalGlueingModuleComplexBeta S f M) :=
  (formalGlueingModuleComplexAlpha S f M).codRestrict _ fun x ↦ by
    change formalGlueingModuleComplexBeta S f M (formalGlueingModuleComplexAlpha S f M x) = 0
    simpa using LinearMap.congr_fun (formalGlueingModuleComplex_comp_eq_zero S f M) x

private noncomputable def formalGlueingH0ToKerBeta
    (M : ModuleCat R) :
    ((formalGlueingH0 S f).obj ((formalGlueingCan S f).obj M)) →ₗ[R]
      LinearMap.ker (formalGlueingModuleComplexBeta S f M) := by
  refine
    { toFun := fun x ↦ ⟨((formalGlueingCanBaseIso M).hom.hom x.1.1, x.1.2.1), by sorry⟩
      map_add' := by sorry
      map_smul' := by sorry }

private noncomputable def formalGlueingKerBetaToH0
    (M : ModuleCat R) :
    LinearMap.ker (formalGlueingModuleComplexBeta S f M) →ₗ[R]
      ((formalGlueingH0 S f).obj ((formalGlueingCan S f).obj M)) := by
  refine
    { toFun := fun x ↦
        ⟨((formalGlueingCanBaseIso M).inv.hom x.1.1, ⟨x.1.2, by sorry⟩), by sorry⟩
      map_add' := by sorry
      map_smul' := by sorry }

private noncomputable def formalGlueingH0KerBetaLinearEquiv
    (M : ModuleCat R) :
    ((formalGlueingH0 S f).obj ((formalGlueingCan S f).obj M)) ≃ₗ[R]
      LinearMap.ker (formalGlueingModuleComplexBeta S f M) :=
  LinearEquiv.ofLinear
    (formalGlueingH0ToKerBeta f M)
    (formalGlueingKerBetaToH0 f M)
    (by sorry)
    (by sorry)

private noncomputable def formalGlueingCanH0LinearEquiv_of_flat_of_quotientMap_bijective
    (hflat : (algebraMap R S).Flat)
    (hquot :
      let I : Ideal R := Ideal.span (Set.range f)
      Function.Bijective
        (Ideal.quotientMap (Ideal.map (algebraMap R S) I) (algebraMap R S) Ideal.le_comap_map))
    (M : ModuleCat R) :
    M ≃ₗ[R] ((formalGlueingH0 S f).obj ((formalGlueingCan S f).obj M)) := by
  let α := formalGlueingModuleComplexAlpha S f M
  let β := formalGlueingModuleComplexBeta S f M
  let α' : M →ₗ[R] LinearMap.ker (formalGlueingModuleComplexBeta S f M) :=
    formalGlueingAlphaToKerBeta f M
  have hExact : (formalGlueingModuleComplex S f M).Exact :=
    (formalGlueingModuleComplex_exact_of_flat_of_quotientMap_bijective M f hflat hquot).1
  have hMono : Mono (formalGlueingModuleComplex S f M).f :=
    (formalGlueingModuleComplex_exact_of_flat_of_quotientMap_bijective M f hflat hquot).2
  have hRangeKer : LinearMap.range α = LinearMap.ker β := by
    simpa [formalGlueingModuleComplex, α, β] using
      ShortComplex.Exact.moduleCat_range_eq_ker hExact
  have hInjective : Function.Injective α' := by
    intro x y hxy
    have hα : α x = α y := by
      exact congrArg Subtype.val hxy
    have hαInjective : Function.Injective α := by
      simpa [formalGlueingModuleComplex, α] using
        (ModuleCat.mono_iff_injective (formalGlueingModuleComplex S f M).f).1 hMono
    exact hαInjective hα
  have hSurjective : Function.Surjective α' := by
    intro y
    have hy : y.1 ∈ LinearMap.range α := by
      simpa [hRangeKer] using y.2
    rcases hy with ⟨x, hx⟩
    refine ⟨x, ?_⟩
    apply Subtype.ext
    exact hx
  exact
    (LinearEquiv.ofBijective α' ⟨hInjective, hSurjective⟩).trans
      (formalGlueingH0KerBetaLinearEquiv f M).symm

-- Proof sketch: identify `H⁰(Can(M))` with the kernel of the second map `β` in the formal
-- glueing module complex. Lemma `15.90.9` gives `range(α) = ker(β)` and injectivity of `α`, so
-- the canonical map `M → ker(β)` is a linear equivalence. Transport this through the kernel-level
-- bridge to obtain the desired componentwise isomorphism.
-- Lemma `15.90.9` identifies the unit map `M ⟶ H^0(Can(M))` with the first map in the formal
-- glueing complex and proves that it is an isomorphism under the flatness and quotient
-- hypotheses, yielding a natural isomorphism `Can ⋙ H^0 ≅ 𝟭`.
/-- Lemma 15.90.12: assume `φ : R → S` is a flat ring map and `I = (f₁, \ldots, fₜ) ⊂ R` is an
ideal such that `R/I → S/IS` is an isomorphism. Then the degree-zero functor `H^0` of Remark
15.90.10 is a left quasi-inverse to the canonical functor `Can`. In the formalization, the
right-adjoint owner is already the canonical functor `formalGlueingH0 R S f` from Remark
`15.90.10`, so the content here is the natural isomorphism
`formalGlueingCan S f ⋙ formalGlueingH0 S f ≅ 𝟭`. -/
noncomputable def formalGlueingH0_leftQuasiInverse_of_flat_of_quotientMap_bijective
    (hflat : (algebraMap R S).Flat)
    (hquot :
      let I : Ideal R := Ideal.span (Set.range f)
      Function.Bijective
        (Ideal.quotientMap (Ideal.map (algebraMap R S) I) (algebraMap R S) Ideal.le_comap_map)) :
    formalGlueingCan S f ⋙ formalGlueingH0 S f ≅ 𝟭 (ModuleCat R) :=
  NatIso.ofComponents
    (fun M ↦
      (formalGlueingCanH0LinearEquiv_of_flat_of_quotientMap_bijective
        f hflat hquot M).symm.toModuleIso)
    (by
      intro M N φ
      ext x
      sorry)

end

/-! ### Lemma_15_90_13 (from Chap15) -/
noncomputable section

open CategoryTheory
open CategoryTheory.Limits

universe u w

section

variable {R : Type u} [CommRing R]
variable {S : Type u} [CommRing S] [Algebra R S]
variable {t : ℕ} (f : Fin t → R)

/- Domain-style sampling:
- primary domain: formal glueing for module categories, with the genuine glueing category carrying
  comparison and overlap isomorphisms.
- inspected owner declarations:
  `FormalGlueingDatum`,
  `FormalGlueingDatum.Hom`,
  `AwayModuleGlueing`,
  `LocalizedModule.equivTensorProduct`,
  `formalGlueingCan`.
- best owner abstraction:
  the source-facing category `FormalGlueingDatum f` from `Remark 15.90.10`, with the overlap side
  built from the chapter-local localization-glueing owner `AwayModuleGlueing` and with genuine
  glueing morphisms encoded by `FormalGlueingDatum.Hom`.
- primitive data:
  the base `S`-module, the localized `R_(fᵢ)`-modules, the comparison isomorphisms, and the
  overlap isomorphisms.
- derived API in this file:
  exactness of `formalGlueingCan S f` under flatness and preservation of colimits by
  `formalGlueingCan S f`.
- layer:
  `source-facing`; this lemma is about the actual glueing category `Glue(R → S, f₁, …, fₜ)`, not a
  surrogate product presentation.
-/

-- Proof sketch: under flatness, localization and tensor product are exact on the comparison and
-- overlap terms, so the canonical functor `Can` is exact on the abelian glueing category.
/-- Lemma 15.90.13 (2): if `R → S` is flat, then the canonical formal glueing functor `Can` is
exact. -/
theorem formalGlueingCan_exact [Module.Flat R S] :
    exactFunctor (ModuleCat.{max u w} R) (Glue S f) (formalGlueingCan S f) := by
  sorry

/-- Lemma 15.90.13 (3): the canonical formal glueing functor preserves all colimits because it is
a left adjoint by Lemma `15.90.11`. -/
noncomputable instance formalGlueingCan_preservesColimits :
    PreservesColimits (formalGlueingCan S f) :=
  inferInstance

end

/-! ### Lemma_15_90_14 (from Chap15) -/
open CategoryTheory

noncomputable section

universe u v

section

variable {R : Type u} [CommRing R]
variable {S : Type u} [CommRing S] [Algebra R S]
variable {t : ℕ} (f : Fin t → R)

/- Domain-style sampling for 15.90.14:
- primary domain: formal glueing for module categories and categorical equivalences;
- sampled owner declarations:
  `Glue`,
  `formalGlueingCan`,
  `formalGlueingCanAdjunction`,
  `Functor.IsEquivalence`;
- best owner abstraction: the source-facing statement should be the equivalence witness for the
  canonical functor `formalGlueingCan S f`;
- primitive data: only the canonical functor `formalGlueingCan S f` and the hypotheses
  `[Module.Flat R S]` and `Ideal.span (Set.range f) = ⊤`;
- derived API: the typeclass instance below. Any inverse functor and unit/counit isomorphisms are
  already provided canonically by `Functor.inv` and `Functor.asEquivalence`, so they should not be
  re-exposed here as parallel local owners.

Source/core/bridge triage:
- `source-facing`: `formalGlueingCan_isEquivalence_of_flat_of_span_eq_top`;
- `core/canonical`: `Functor.IsEquivalence`;
- `bridge/view`: the instance `formalGlueingCan_isEquivalence`.
-/

-- Proof sketch: combine the right quasi-inverse from Lemma `15.90.12` with the module glueing
-- existence-and-uniqueness statement from Algebra, Lemma `10.24.5`. When `Ideal.span (Set.range f)
-- = ⊤`, every formal glueing datum comes from a unique `R`-module, giving essential surjectivity of
-- `Can`; together with the quasi-inverse statement of Lemma `15.90.12`, this yields an equivalence.
/-- Lemma 15.90.14: if `φ : R → S` is a flat ring map and the generators `f₁, \ldots, fₜ`
generate the unit ideal of `R`, then the canonical formal glueing functor
`Can : Mod_R ⥤ Glue(R → S, f₁, …, fₜ)` is an equivalence of categories, where
`Glue(R → S, f₁, …, fₜ)` is the genuine formal glueing category from Remark `15.90.10`. -/
theorem formalGlueingCan_isEquivalence_of_flat_of_span_eq_top [Module.Flat R S]
    (hspan : Ideal.span (Set.range f) = ⊤) :
    Functor.IsEquivalence (formalGlueingCan S f) := sorry

/-- The equivalence instance attached to formal glueing when the `fᵢ` generate the unit ideal. -/
noncomputable instance formalGlueingCan_isEquivalence [Module.Flat R S]
    (hspan : Ideal.span (Set.range f) = ⊤) :
    Functor.IsEquivalence (formalGlueingCan S f) :=
  formalGlueingCan_isEquivalence_of_flat_of_span_eq_top f hspan

end
