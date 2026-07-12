import StacksProject_2024.Chap10.Lemma_10_24_5

-- Declarations for this item will be appended below by the statement pipeline.

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

/-- Helper for Remark 15.90.10: tensoring an already localized module map with the identity on the
base algebra sends the identity map to the identity morphism. -/
@[simp] private theorem localTensorModuleCatMap_id
    (A : Type u) [CommRing A] [Algebra R A]
    (a : R) (M : Type w) [AddCommGroup M] [Module (Localization.Away a) M]
    [Module R M] [IsScalarTower R (Localization.Away a) M] :
    localTensorModuleCatMap A a (LinearMap.id : M →ₗ[R] M) =
      𝟙 (localTensorModuleCat A a M) := by
  -- Route correction: the localization/tensor owner already computes pointwise, so extensionality
  -- reduces the identity law to reflexivity on the tensor module.
  ext x
  rfl

/-- Helper for Remark 15.90.10: tensoring localized maps with the identity on the base algebra
preserves composition. -/
@[simp] private theorem localTensorModuleCatMap_comp
    (A : Type u) [CommRing A] [Algebra R A]
    (a : R) {M N P : Type w} [AddCommGroup M] [Module (Localization.Away a) M]
    [Module R M] [IsScalarTower R (Localization.Away a) M]
    [AddCommGroup N] [Module (Localization.Away a) N] [Module R N]
    [IsScalarTower R (Localization.Away a) N]
    [AddCommGroup P] [Module (Localization.Away a) P] [Module R P]
    [IsScalarTower R (Localization.Away a) P]
    (g : M →ₗ[R] N) (h : N →ₗ[R] P) :
    localTensorModuleCatMap A a (h.comp g) =
      localTensorModuleCatMap A a g ≫ localTensorModuleCatMap A a h := by
  -- The owner-level localization/tensor construction composes definitionally on the tensor module.
  ext x
  rfl

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

/-- Helper for Remark 15.90.10: the base-change/localization comparison sends a denominator-`1`
pure tensor to the tensor of the corresponding denominator-`1` localized element. -/
@[simp] private theorem awayBaseChangeComparisonIso_hom_apply_mk_tmul
    (A : Type u) [CommRing A] [Algebra R A]
    (a : R) (M : ModuleCat.{max u w} R) (x : A) (m : M) :
    (awayBaseChangeComparisonIso A a M).hom.hom
        (LocalizedModule.mk (x ⊗ₜ[R] m) 1) =
      ((LocalizedModule.mk m 1 : Away a M) ⊗ₜ[R] x) := by
  -- TODO: normalize the staged localization/tensor comparison to the explicit
  -- `LocalizedModule.equivTensorProduct` generator formula `x ⊗ m ↦ mk m 1 ⊗ x`.
  sorry

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
  -- Localizing the identity map is still the identity on the away module.
  ext x
  change (LocalizedModule.map (Submonoid.powers (f i)) (LinearMap.id : X.base →ₗ[R] X.base)) x = x
  induction x using LocalizedModule.induction_on with
  | _ y s =>
      rw [LocalizedModule.map_mk]
      rfl

@[simp] private theorem formalGlueingBaseMap_comp {f : Fin t → R}
    {X Y Z : FormalGlueingDatum S f} (i : Fin t) (φ : X.base ⟶ Y.base) (ψ : Y.base ⟶ Z.base) :
    formalGlueingBaseMap i (φ ≫ ψ) = formalGlueingBaseMap i φ ≫ formalGlueingBaseMap i ψ := by
  -- Localization carries composition of base maps to composition of localized maps.
  ext x
  change
    (LocalizedModule.map (Submonoid.powers (f i)) ((ψ.hom.restrictScalars R).comp (φ.hom.restrictScalars R))) x =
      ((LocalizedModule.map (Submonoid.powers (f i)) (ψ.hom.restrictScalars R)).comp
        (LocalizedModule.map (Submonoid.powers (f i)) (φ.hom.restrictScalars R))) x
  induction x using LocalizedModule.induction_on with
  | _ y s =>
      rw [LinearMap.comp_apply]
      rw [LocalizedModule.map_mk, LocalizedModule.map_mk, LocalizedModule.map_mk]
      rfl

@[simp] private theorem formalGlueingTensorMap_id {f : Fin t → R} (X : FormalGlueingDatum S f)
    (i : Fin t) :
    formalGlueingTensorMap i (𝟙 (X.glue.localModule i)) = 𝟙 _ := by
  -- The tensor-side identity law is the owner-level identity law for localized tensor maps.
  simpa [formalGlueingTensorMap] using
    localTensorModuleCatMap_id S (f i) (X.glue.localModule i)

@[simp] private theorem formalGlueingTensorMap_comp {f : Fin t → R}
    {X Y Z : FormalGlueingDatum S f} (i : Fin t)
    (φ : X.glue.localModule i ⟶ Y.glue.localModule i)
    (ψ : Y.glue.localModule i ⟶ Z.glue.localModule i) :
    formalGlueingTensorMap i (φ ≫ ψ) = formalGlueingTensorMap i φ ≫ formalGlueingTensorMap i ψ := by
  -- The tensor-side composition law is the owner-level composition law for localized tensor maps.
  simpa [formalGlueingTensorMap] using
    localTensorModuleCatMap_comp S (f i)
      ((φ.hom.restrictScalars R)) ((ψ.hom.restrictScalars R))

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

/-- Helper for Remark 15.90.10: localizing the identity equivalence does not change the away
module. -/
@[simp] private theorem awayLocalizeLinearEquiv_refl
    (a : R) (M : Type w) [AddCommGroup M] [Module R M] :
    awayLocalizeLinearEquiv a (LinearEquiv.refl R M) = LinearEquiv.refl R (Away a M) := by
  -- Both sides act identically on localization generators, so the owner-level equivalences agree.
  ext x
  induction x using LocalizedModule.induction_on with
  | _ y s =>
      simp [awayLocalizeLinearEquiv]

/-- Helper for Remark 15.90.10: maps out of an away localization are determined by their values
on the canonical localization map. -/
private theorem away_hom_ext_of_comp_mkLinearMap_eq
    (a : R) {M N : Type w} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (hS : ∀ s : Submonoid.powers a, IsUnit (algebraMap R (Module.End R N) s))
    {g h : Away a M →ₗ[R] N}
    (hcomp : g.comp (LocalizedModule.mkLinearMap (Submonoid.powers a) M) =
      h.comp (LocalizedModule.mkLinearMap (Submonoid.powers a) M)) :
    g = h := by
  -- The away-localization universal property identifies maps once their restrictions to the
  -- original module agree along `mkLinearMap`.
  simpa using
    (IsLocalizedModule.is_universal (Submonoid.powers a)
      (LocalizedModule.mkLinearMap (Submonoid.powers a) M)
      (g.comp (LocalizedModule.mkLinearMap (Submonoid.powers a) M))
      hS).unique rfl hcomp.symm

/-- Helper for Remark 15.90.10: the base-change/localization comparison is natural in the
underlying module map. -/
private theorem awayBaseChangeComparisonIso_naturality
    (A : Type u) [CommRing A] [Algebra R A]
    (a : R) {M N : ModuleCat.{max u w} R} (φ : M ⟶ N) :
    (awayBaseChangeComparisonIso A a N).hom.hom.comp
        (LocalizedModule.map (Submonoid.powers a)
          (((ModuleCat.extendScalars (algebraMap R A)).map φ).hom.restrictScalars R)) =
      (localTensorModuleCatMap A a
          ((LocalizedModule.map (Submonoid.powers a) φ.hom).restrictScalars R)).hom.comp
        (awayBaseChangeComparisonIso A a M).hom.hom := by
  -- TODO: apply `away_hom_ext_of_comp_mkLinearMap_eq` with codomain `Away a N ⊗[R] A`,
  -- reduce to pure tensors in the scalar-extension owner, and close each generator with
  -- `awayBaseChangeComparisonIso_hom_apply_mk_tmul`.
  sorry

/-- Helper for Remark 15.90.10: if `r` divides the element inverted in an away localization, then
`r` acts invertibly on the localized module. -/
private theorem away_module_end_isUnit_of_dvd
    (x r : R) (M : Type w) [AddCommGroup M] [Module R M] (h : r ∣ x) :
    IsUnit (algebraMap R (Module.End R (Away x M)) r) := by
  -- In the away localization of `x`, any divisor of `x` is already invertible in the scalar ring,
  -- and hence acts by an invertible endomorphism on the localized module.
  have h' : IsUnit (algebraMap R (Localization.Away x) r) :=
    IsLocalization.Away.isUnit_of_dvd x h
  let lsmulAway : Localization.Away x →ₐ[R] Module.End R (Away x M) :=
    Algebra.lsmul R R (Away x M)
  simpa [Algebra.smul_def] using h'.map lsmulAway

/-- Helper for Remark 15.90.10: every power of the inverted element acts invertibly on its away
localization. -/
private theorem away_module_end_isUnit_of_self_powers
    (a : R) (M : Type w) [AddCommGroup M] [Module R M] :
    ∀ s : Submonoid.powers a, IsUnit (algebraMap R (Module.End R (Away a M)) s) := by
  -- The identity map on an away localization is itself a localization map, so its `map_units`
  -- field supplies the needed invertibility.
  intro s
  simpa using
    (isLocalizedModule_id (Submonoid.powers a) (Away a M) (Localization.Away a)).map_units s

/-- Helper for Remark 15.90.10: every power of the left factor acts invertibly on the localization
away from the product. -/
private theorem away_module_end_isUnit_of_left_factor_powers
    (a b : R) (M : Type w) [AddCommGroup M] [Module R M] :
    ∀ s : Submonoid.powers a, IsUnit (algebraMap R (Module.End R (Away (a * b) M)) s) := by
  -- It suffices to note that `a` divides `ab`, hence `a` is invertible after localizing away from
  -- `ab`, and so are all of its powers.
  intro s
  rcases (Submonoid.mem_powers_iff s.1 a).mp s.2 with ⟨n, hn⟩
  have ha :
      IsUnit (algebraMap R (Module.End R (Away (a * b) M)) a) := by
    simpa using away_module_end_isUnit_of_dvd (x := a * b) (r := a) (M := M) (dvd_mul_right a b)
  rw [← hn]
  simpa using ha.pow n

/-- Helper for Remark 15.90.10: every power of the right factor acts invertibly on the localization
away from the product. -/
private theorem away_module_end_isUnit_of_right_factor_powers
    (a b : R) (M : Type w) [AddCommGroup M] [Module R M] :
    ∀ s : Submonoid.powers b, IsUnit (algebraMap R (Module.End R (Away (a * b) M)) s) := by
  -- This is the symmetric version of the previous left-factor statement.
  intro s
  rcases (Submonoid.mem_powers_iff s.1 b).mp s.2 with ⟨n, hn⟩
  have hb :
      IsUnit (algebraMap R (Module.End R (Away (a * b) M)) b) := by
    simpa [mul_comm] using
      away_module_end_isUnit_of_dvd (x := a * b) (r := b) (M := M) (dvd_mul_left b a)
  rw [← hn]
  simpa using hb.pow n

/-- Helper for Remark 15.90.10: reindexing an away-localization along an equality preserves the
denominator-`1` generator. -/
private theorem formalGlueingCan_awayEqLinearEquiv_apply_mk_one
    (M : Type w) [AddCommGroup M] [Module R M] {a b : R} (h : a = b) (m : M) :
    awayEqLinearEquiv M h (LocalizedModule.mk m 1 : Away a M) =
      (LocalizedModule.mk m 1 : Away b M) := by
  -- Reindexing only changes the inverted element, so the standard generator is unchanged.
  cases h
  rfl

/-- Helper for Remark 15.90.10: the iterated away-localization equivalence sends the
denominator-`1` generator to the corresponding denominator-`1` generator in the direct
localization. -/
private theorem formalGlueingCan_iteratedLocalizedIso_apply_mk_one
    (a b : R) (M : Type w) [AddCommGroup M] [Module (Localization.Away a) M]
    [Module R M] [IsScalarTower R (Localization.Away a) M] (m : M) :
    iteratedLocalizedIso a b M (LocalizedModule.mk m 1 : LocalizedModule.Away b M) =
      (LocalizedModule.mk m 1 : LocalizedModule.Away (a * b) M) := by
  -- Expand the iterated equivalence and compute both owner-level localization maps on the
  -- denominator-`1` generator.
  change
    awayMulLinearEquiv a b M
      ((LocalizedModule.map (Submonoid.powers b) ((alreadyLocalizedLinearEquiv a M).symm.toLinearMap))
        (LocalizedModule.mk m 1 : LocalizedModule.Away b M)) =
      (LocalizedModule.mk m 1 : LocalizedModule.Away (a * b) M)
  rw [LocalizedModule.map_mk]
  have hmk :
      (alreadyLocalizedLinearEquiv a M).symm m =
        (LocalizedModule.mk m 1 : LocalizedModule.Away a M) := by
    -- Characterize the inverse of the already-localized equivalence on the standard generator.
    apply (alreadyLocalizedLinearEquiv a M).injective
    simpa using
      (IsLocalizedModule.linearEquiv_apply (Submonoid.powers a)
        (LocalizedModule.mkLinearMap (Submonoid.powers a) M)
        (LinearMap.id : M →ₗ[R] M) m).symm
  simpa [hmk] using
    (IsLocalizedModule.linearEquiv_apply
      (Submonoid.powers b ⊔ Submonoid.powers a)
      (iteratedLocalizedModuleMkLinearMap (Submonoid.powers b) (Submonoid.powers a) M)
      (LocalizedModule.mkLinearMap (Submonoid.powers (a * b)) M)
      m)

/-- Helper for Remark 15.90.10: the inverse direct away-localization equivalence sends the direct
denominator-`1` generator to the corresponding iterated denominator-`1` generator. -/
private theorem formalGlueingCan_awayMulLinearEquiv_symm_apply_mk_one
    (a b : R) (M : Type w) [AddCommGroup M] [Module R M] (m : M) :
    (awayMulLinearEquiv a b M).symm
        (LocalizedModule.mk m 1 : LocalizedModule.Away (a * b) M) =
      (LocalizedModule.mk (LocalizedModule.mk m 1) 1 :
        LocalizedModule.Away b (LocalizedModule.Away a M)) := by
  -- Apply the forward direct-localization equivalence to reduce to its defining action on the
  -- iterated denominator-`1` generator.
  apply (awayMulLinearEquiv a b M).injective
  simpa using
    (IsLocalizedModule.linearEquiv_apply
      (Submonoid.powers b ⊔ Submonoid.powers a)
      (iteratedLocalizedModuleMkLinearMap (Submonoid.powers b) (Submonoid.powers a) M)
      (LocalizedModule.mkLinearMap (Submonoid.powers (a * b)) M)
      m).symm

/-- Helper for Remark 15.90.10: the `i`-side transport from `(M_{f_i})_{f_j}` to `M_{f_i f_j}`
sends the standard generator to the direct generator. -/
private theorem formalGlueingCan_leftToDirect_apply_mk_one
    (f : Fin t → R) (M : ModuleCat.{max u w} R) (i j : Fin t) (m : M) :
    (((iteratedLocalizedIso (f i) (f j) (LocalizedModule.Away (f i) M)).symm ≪≫ₗ
        awayMulLinearEquiv (f i) (f j) M)
      (LocalizedModule.mk
        (LocalizedModule.mk m 1 : LocalizedModule.Away (f i) M) 1 :
        LocalizedModule.Away (f i * f j) (LocalizedModule.Away (f i) M))) =
      (LocalizedModule.mk m 1 : LocalizedModule.Away (f i * f j) M) := by
  -- Rewrite through the inverse iterated-localization equivalence and then evaluate the direct
  -- localization map on the denominator-`1` generator.
  rw [LinearEquiv.trans_apply]
  calc
    (awayMulLinearEquiv (f i) (f j) M)
        ((iteratedLocalizedIso (f i) (f j) (LocalizedModule.Away (f i) M)).symm
          (LocalizedModule.mk
            (LocalizedModule.mk m 1 : LocalizedModule.Away (f i) M) 1 :
            LocalizedModule.Away (f i * f j) (LocalizedModule.Away (f i) M))) =
      (awayMulLinearEquiv (f i) (f j) M)
        (LocalizedModule.mk
          (LocalizedModule.mk m 1 : LocalizedModule.Away (f i) M) 1 :
          LocalizedModule.Away (f j) (LocalizedModule.Away (f i) M)) := by
        congr 1
        apply (iteratedLocalizedIso (f i) (f j) (LocalizedModule.Away (f i) M)).injective
        rw [LinearEquiv.apply_symm_apply]
        simpa using
          (formalGlueingCan_iteratedLocalizedIso_apply_mk_one
            (a := f i) (b := f j) (M := LocalizedModule.Away (f i) M)
            (m := (LocalizedModule.mk m 1 : LocalizedModule.Away (f i) M))).symm
    _ = (LocalizedModule.mk m 1 : LocalizedModule.Away (f i * f j) M) := by
        simpa using
          (IsLocalizedModule.linearEquiv_apply
            (Submonoid.powers (f j) ⊔ Submonoid.powers (f i))
            (iteratedLocalizedModuleMkLinearMap
              (Submonoid.powers (f j)) (Submonoid.powers (f i)) M)
            (LocalizedModule.mkLinearMap (Submonoid.powers (f i * f j)) M)
            m)

/-- Helper for Remark 15.90.10: the `j`-side transport from `(M_{f_j})_{f_i}` to `M_{f_i f_j}`
sends the standard generator to the direct generator. -/
private theorem formalGlueingCan_rightToDirect_apply_mk_one
    (f : Fin t → R) (M : ModuleCat.{max u w} R) (i j : Fin t) (m : M) :
    ((((awayEqLinearEquiv (LocalizedModule.Away (f j) M) (mul_comm (f i) (f j))) ≪≫ₗ
        (iteratedLocalizedIso (f j) (f i) (LocalizedModule.Away (f j) M)).symm ≪≫ₗ
        awayMulLinearEquiv (f j) (f i) M) ≪≫ₗ
      awayEqLinearEquiv M (mul_comm (f j) (f i)))
      (LocalizedModule.mk
        (LocalizedModule.mk m 1 : LocalizedModule.Away (f j) M) 1 :
        LocalizedModule.Away (f i * f j) (LocalizedModule.Away (f j) M))) =
      (LocalizedModule.mk m 1 : LocalizedModule.Away (f i * f j) M) := by
  -- Rewrite to the swapped product, use the already computed left transport there, and rewrite
  -- back to the original pairwise overlap.
  calc
    (awayEqLinearEquiv M (mul_comm (f j) (f i)))
        (((iteratedLocalizedIso (f j) (f i) (LocalizedModule.Away (f j) M)).symm ≪≫ₗ
            awayMulLinearEquiv (f j) (f i) M)
          ((awayEqLinearEquiv (LocalizedModule.Away (f j) M) (mul_comm (f i) (f j)))
            (LocalizedModule.mk
              (LocalizedModule.mk m 1 : LocalizedModule.Away (f j) M) 1 :
              LocalizedModule.Away (f i * f j) (LocalizedModule.Away (f j) M)))) =
      (awayEqLinearEquiv M (mul_comm (f j) (f i)))
        (((iteratedLocalizedIso (f j) (f i) (LocalizedModule.Away (f j) M)).symm ≪≫ₗ
            awayMulLinearEquiv (f j) (f i) M)
          (LocalizedModule.mk
            (LocalizedModule.mk m 1 : LocalizedModule.Away (f j) M) 1 :
            LocalizedModule.Away (f j * f i) (LocalizedModule.Away (f j) M))) := by
        rw [formalGlueingCan_awayEqLinearEquiv_apply_mk_one
          (M := LocalizedModule.Away (f j) M) (h := mul_comm (f i) (f j))
          (m := (LocalizedModule.mk m 1 : LocalizedModule.Away (f j) M))]
    _ = (awayEqLinearEquiv M (mul_comm (f j) (f i)))
          (LocalizedModule.mk m 1 : LocalizedModule.Away (f j * f i) M) := by
        congr 1
        simpa using
          (formalGlueingCan_leftToDirect_apply_mk_one (f := f) (M := M) (i := j) (j := i) (m := m))
    _ = (LocalizedModule.mk m 1 : LocalizedModule.Away (f i * f j) M) := by
        simpa using
          (formalGlueingCan_awayEqLinearEquiv_apply_mk_one
            (M := M) (h := mul_comm (f j) (f i)) (m := m))

/-- Helper for Remark 15.90.10: the `i`-side pairwise overlap is transported to the common direct
localization owner `Away (f_i f_j) M`. -/
private noncomputable abbrev formalGlueingCanLeftToDirect
    (f : Fin t → R) (M : ModuleCat.{max u w} R) (i j : Fin t) :
    Away (f i * f j) (Away (f i) M) ≃ₗ[Localization.Away (f i * f j)]
      Away (f i * f j) M :=
  letI := localizedAwayId (f i) M
  (((iteratedLocalizedIso (f i) (f j) (Away (f i) M)).symm ≪≫ₗ
      awayMulLinearEquiv (f i) (f j) M).extendScalarsOfIsLocalization
        (Submonoid.powers (f i * f j)) (Localization.Away (f i * f j)))

/-- Helper for Remark 15.90.10: the `j`-side pairwise overlap is transported to the same direct
localization owner `Away (f_i f_j) M`. -/
private noncomputable abbrev formalGlueingCanRightToDirect
    (f : Fin t → R) (M : ModuleCat.{max u w} R) (i j : Fin t) :
    Away (f i * f j) (Away (f j) M) ≃ₗ[Localization.Away (f i * f j)]
      Away (f i * f j) M :=
  letI := localizedAwayId (f j) M
  (((awayEqLinearEquiv (Away (f j) M) (mul_comm _ _) ≪≫ₗ
        (iteratedLocalizedIso (f j) (f i) (Away (f j) M)).symm ≪≫ₗ
        awayMulLinearEquiv (f j) (f i) M) ≪≫ₗ
      awayEqLinearEquiv M (mul_comm _ _)).extendScalarsOfIsLocalization
        (Submonoid.powers (f i * f j)) (Localization.Away (f i * f j)))

/-- Helper for Remark 15.90.10: the extended `i`-side transport to the direct pairwise
localization sends the standard generator to the direct denominator-`1` generator. -/
private theorem formalGlueingCanLeftToDirect_apply_generator
    (f : Fin t → R) (M : ModuleCat.{max u w} R) (i j : Fin t) (m : M) :
    formalGlueingCanLeftToDirect f M i j
        (LocalizedModule.mk (LocalizedModule.mk m 1) 1) =
      (LocalizedModule.mk m 1 : LocalizedModule.Away (f i * f j) M) := by
  -- The extended localization equivalence acts by its underlying `R`-linear map on the standard
  -- generator, so the earlier owner-level computation applies unchanged.
  simpa [formalGlueingCanLeftToDirect, LinearEquiv.extendScalarsOfIsLocalization_apply] using
    formalGlueingCan_leftToDirect_apply_mk_one f M i j m

/-- Helper for Remark 15.90.10: the extended `j`-side transport to the direct pairwise
localization sends the standard generator to the same direct denominator-`1` generator. -/
private theorem formalGlueingCanRightToDirect_apply_generator
    (f : Fin t → R) (M : ModuleCat.{max u w} R) (i j : Fin t) (m : M) :
    formalGlueingCanRightToDirect f M i j
        (LocalizedModule.mk (LocalizedModule.mk m 1) 1) =
      (LocalizedModule.mk m 1 : LocalizedModule.Away (f i * f j) M) := by
  -- As on the left side, extension of scalars does not change the value on the canonical
  -- denominator-`1` generator.
  simpa [formalGlueingCanRightToDirect, LinearEquiv.extendScalarsOfIsLocalization_apply] using
    formalGlueingCan_rightToDirect_apply_mk_one f M i j m

/-- Helper for Remark 15.90.10: the inverse of the expanded right direct-localization transport
sends the direct denominator-`1` generator back to the iterated generator on the `j`-side. -/
private theorem formalGlueingCan_expanded_right_transport_symm_apply_mk_one
    (f : Fin t → R) (M : ModuleCat.{max u w} R) (i j : Fin t) (m : M) :
    (((((awayEqLinearEquiv (LocalizedModule.Away (f j) M) (mul_comm (f i) (f j))) ≪≫ₗ
          (iteratedLocalizedIso (f j) (f i) (LocalizedModule.Away (f j) M)).symm ≪≫ₗ
          awayMulLinearEquiv (f j) (f i) M) ≪≫ₗ
        awayEqLinearEquiv M (mul_comm (f j) (f i))).symm).extendScalarsOfIsLocalization
        (Submonoid.powers (f i * f j)) (Localization.Away (f i * f j)))
      (LocalizedModule.mk m 1 : LocalizedModule.Away (f i * f j) M) =
        (LocalizedModule.mk
          (LocalizedModule.mk m 1 : LocalizedModule.Away (f j) M) 1 :
          LocalizedModule.Away (f i * f j) (LocalizedModule.Away (f j) M)) := by
  -- Apply the forward right transport to both sides so the goal reduces to the direct-generator
  -- formula already proved above.
  let e :
      LocalizedModule.Away (f i * f j) (LocalizedModule.Away (f j) M) ≃ₗ[R]
        LocalizedModule.Away (f i * f j) M :=
    (((awayEqLinearEquiv (LocalizedModule.Away (f j) M) (mul_comm (f i) (f j))) ≪≫ₗ
          (iteratedLocalizedIso (f j) (f i) (LocalizedModule.Away (f j) M)).symm ≪≫ₗ
          awayMulLinearEquiv (f j) (f i) M) ≪≫ₗ
        awayEqLinearEquiv M (mul_comm (f j) (f i)))
  apply (LinearEquiv.extendScalarsOfIsLocalization
    (Submonoid.powers (f i * f j)) (Localization.Away (f i * f j)) e).injective
  -- The extended equivalence acts by the underlying map on canonical localization generators.
  rw [LinearEquiv.extendScalarsOfIsLocalization_apply, LinearEquiv.extendScalarsOfIsLocalization_apply]
  rw [LinearEquiv.apply_symm_apply]
  simpa [e] using
    (formalGlueingCan_rightToDirect_apply_mk_one (f := f) (M := M) (i := i) (j := j) (m := m)).symm

/-- Helper for Remark 15.90.10: on denominator-`1` generators, the canonical overlap equivalence
for `Can` is the evident identification of the two iterated localizations. -/
private theorem formalGlueingCan_overlapIso_mk_one
    (f : Fin t → R) (M : ModuleCat.{max u w} R) (i j : Fin t) (m : M) :
    formalGlueingCanOverlapLinearEquiv f M i j
        (LocalizedModule.mk (LocalizedModule.mk m 1) 1) =
      LocalizedModule.mk (LocalizedModule.mk m 1) 1 := by
  -- Evaluate the left direct-localization transport first, then rewrite the inverse right
  -- transport on the resulting direct generator.
  simp only [formalGlueingCanOverlapLinearEquiv, LinearEquiv.extendScalarsOfIsLocalization_apply,
    LinearEquiv.trans_apply]
  have hleft :
      (awayMulLinearEquiv (f i) (f j) M)
          ((iteratedLocalizedIso (f i) (f j) (LocalizedModule.Away (f i) M)).symm
            (LocalizedModule.mk
              (LocalizedModule.mk m 1 : LocalizedModule.Away (f i) M) 1)) =
        (LocalizedModule.mk m 1 : LocalizedModule.Away (f i * f j) M) := by
    -- This is exactly the previously proved denominator-`1` formula, just in unfolded
    -- `LinearEquiv.trans_apply` form.
    simpa [LinearEquiv.trans_apply] using
      formalGlueingCan_leftToDirect_apply_mk_one f M i j m
  rw [hleft]
  simpa using
    formalGlueingCan_expanded_right_transport_symm_apply_mk_one (f := f) (M := M) (i := i)
      (j := j) (m := m)

/-- Helper for Remark 15.90.10: the `i`-side transport to the common direct pairwise-localized
owner is natural in the underlying module map. -/
private theorem formalGlueingCanLeftToDirect_naturality
    (f : Fin t → R) {M N : ModuleCat.{max u w} R} (φ : M ⟶ N) (i j : Fin t) :
    (formalGlueingCanLeftToDirect f N i j).toLinearMap.comp
        (LocalizedModule.map (Submonoid.powers (f i * f j))
          ((LocalizedModule.map (Submonoid.powers (f i)) φ.hom).restrictScalars R)) =
      (LocalizedModule.map (Submonoid.powers (f i * f j)) φ.hom).comp
        (formalGlueingCanLeftToDirect f M i j).toLinearMap := by
  -- TODO: normalize the outer and inner localization owners explicitly before applying
  -- `away_hom_ext_of_comp_mkLinearMap_eq`; the remaining issue is a definitional owner mismatch.
  sorry

/-- Helper for Remark 15.90.10: the `j`-side transport to the common direct pairwise-localized
owner is natural in the underlying module map. -/
private theorem formalGlueingCanRightToDirect_naturality
    (f : Fin t → R) {M N : ModuleCat.{max u w} R} (φ : M ⟶ N) (i j : Fin t) :
    (formalGlueingCanRightToDirect f N i j).toLinearMap.comp
        (LocalizedModule.map (Submonoid.powers (f i * f j))
          ((LocalizedModule.map (Submonoid.powers (f j)) φ.hom).restrictScalars R)) =
      (LocalizedModule.map (Submonoid.powers (f i * f j)) φ.hom).comp
        (formalGlueingCanRightToDirect f M i j).toLinearMap := by
  -- TODO: as on the left side, first rewrite to the concrete common owner
  -- `Away (f_i f_j) N`, then apply the localization universal property on generators.
  sorry

/-- Helper for Remark 15.90.10: the canonical overlap equivalence for `Can` is natural in the
underlying module map after transporting both sides to the common pairwise-localized owner. -/
private theorem formalGlueingCanOverlapLinearEquiv_naturality
    (f : Fin t → R) {M N : ModuleCat.{max u w} R} (φ : M ⟶ N) (i j : Fin t) :
    (formalGlueingCanOverlapLinearEquiv f N i j).toLinearMap.comp
        (LocalizedModule.map (Submonoid.powers (f i * f j))
          ((LocalizedModule.map (Submonoid.powers (f i)) φ.hom).restrictScalars R)) =
      (LocalizedModule.map (Submonoid.powers (f i * f j))
          ((LocalizedModule.map (Submonoid.powers (f j)) φ.hom).restrictScalars R)).comp
        (formalGlueingCanOverlapLinearEquiv f M i j).toLinearMap := by
  -- TODO: transport both sides to the common owner
  -- `Away (f_i f_j) (Away (f_j) N)` before invoking the already proved generator formula.
  sorry

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
    -- TODO: compare the three routes by transporting each triple overlap to the common direct
    -- localization `Away (f i * f j * f k) M`; the remaining blocker is the explicit owner-level
    -- normalization of the triple transport maps, which is not exposed by the imported API.
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
    -- TODO: rewrite both sides of the overlap square into the same localized tensor owner using
    -- `awayBaseChangeComparisonIso` and the canonical overlap equivalence.
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
    -- TODO: after normalizing the public overlap wrapper to the common direct owner, this square
    -- is exactly `formalGlueingCanOverlapLinearEquiv_naturality`.
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
      -- TODO: remove the tautological tensor-congruence wrapper and rewrite the square to the
      -- owner-level equality `awayBaseChangeComparisonIso_naturality`.
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

/-- Helper for Remark 15.90.10: the glued-module map induced by the identity morphism is the
identity on the glued module. -/
private theorem gluedMap_id
    (X : AwayModuleGlueing f) :
    (AwayModuleGlueing.Hom.gluedMap (𝟙 X)) = LinearMap.id := by
  -- Both maps have the same underlying family of local components.
  ext x i
  rfl

/-- Helper for Remark 15.90.10: glued-module maps compose by composing the underlying morphisms of
glueing data. -/
private theorem gluedMap_comp
    {X Y Z : AwayModuleGlueing f} (φ : X ⟶ Y) (ψ : Y ⟶ Z) :
    AwayModuleGlueing.Hom.gluedMap (φ ≫ ψ) = ψ.gluedMap.comp φ.gluedMap := by
  -- The codomain subtype data agree because the componentwise local maps agree.
  ext x i
  rfl

/-- Helper for Remark 15.90.10: each component of the degree-zero compatibility map is natural in
a morphism of formal glueing data. -/
private theorem h0ComparisonComponent_naturality
    {X Y : Glue S f} (φ : X ⟶ Y) (i : Fin t) :
    (h0ComparisonComponent Y i).comp (h0UnderlyingMap φ) =
      (TensorProduct.map ((φ.localMap i).hom.restrictScalars R) (LinearMap.id : S →ₗ[R] S)).comp
        (h0ComparisonComponent X i) := by
  -- Check the base-localization summand and the glued-module summand separately on a source pair.
  apply LinearMap.ext
  intro x
  rcases x with ⟨xBase, xGlue⟩
  change
    ((Y.comparisonIso i).hom.hom.restrictScalars R)
        (LocalizedModule.mk ((φ.base.hom.restrictScalars R) xBase) 1) -
      (TensorProduct.mk R (Y.glue.localModule i) S) (((φ.localMap i).hom) (xGlue.1 i)) 1 =
    TensorProduct.map ((φ.localMap i).hom.restrictScalars R) (LinearMap.id : S →ₗ[R] S)
        (((X.comparisonIso i).hom.hom.restrictScalars R) (LocalizedModule.mk xBase 1) -
          (TensorProduct.mk R (X.glue.localModule i) S) (xGlue.1 i) 1)
  rw [map_sub]
  congr 1
  · -- The comparison square controls the localized base contribution.
    have hcomparison :=
      congrArg
        (fun k ↦ k (LocalizedModule.mk xBase 1 : Away (f i) X.base))
        (φ.comparison_comm i).w
    simpa [formalGlueingBaseMap, formalGlueingTensorMap] using hcomparison

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
      -- Each compatibility component vanishes after applying naturality to an element already in
      -- the source kernel.
      change h0CompatibilityMap Y (h0UnderlyingMap φ x) = 0
      ext i
      have hx :
          h0ComparisonComponent X i x = 0 := by
        exact congrArg (fun g ↦ g i) x.2
      have hnat :=
        congrArg (fun g ↦ g x) (h0ComparisonComponent_naturality φ i)
      simpa [LinearMap.comp_apply, hx] using hnat)

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
      -- The identity acts trivially on both the base term and the glued local term.
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      apply Subtype.ext
      apply Prod.ext
      · rfl
      · apply Subtype.ext
        ext i
        have hglued :=
          congrArg (fun g ↦ g x.1.2) (FormalGlueingDatum.gluedMap_id X.glue)
        simpa using congrArg (fun y : X.glue.gluedModule ↦ y.1 i) hglued
    map_comp := by
      intro X Y Z φ ψ
      -- Composition on `H^0` follows from composition on the base map and on the glued module map.
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      apply Subtype.ext
      apply Prod.ext
      · rfl
      · apply Subtype.ext
        ext i
        have hglued :=
          congrArg (fun g ↦ g x.1.2) (FormalGlueingDatum.gluedMap_comp φ.glue ψ.glue)
        simpa using congrArg (fun y : Z.glue.gluedModule ↦ y.1 i) hglued }

end
