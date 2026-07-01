import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open IsLocalizedModule

universe u

-- `IsLocalizedModule` is available over commutative semirings, but this item is expressed in
-- `ModuleCat`, whose bundled change-of-rings and localization APIs are ring-based.
variable {R : Type u} [CommRing R] (S : Submonoid R)

private def invertibleActionProperty : ObjectProperty (ModuleCat R) :=
  fun M ↦ ∀ s : S, IsUnit (algebraMap R (Module.End R M) s)

private theorem isLocalizedModule_id_of_invertibleAction
    (M : ModuleCat R) (hM : invertibleActionProperty S M) :
    IsLocalizedModule S (LinearMap.id : M →ₗ[R] M) where
  map_units := hM
  surj m := ⟨(m, 1), by simp⟩
  exists_of_eq h := ⟨1, by simpa using h⟩

private def localizedIdProperty : ObjectProperty (ModuleCat R) :=
  fun M ↦ IsLocalizedModule S (LinearMap.id : M →ₗ[R] M)

private theorem localizedIdProperty_iff_invertibleAction (M : ModuleCat R) :
    localizedIdProperty S M ↔ invertibleActionProperty S M := by
  constructor
  · intro h s
    exact h.map_units s
  · intro h
    exact isLocalizedModule_id_of_invertibleAction S M h

/-- Restriction of scalars along `R → S⁻¹R` lands in the full subcategory of `R`-modules whose
identity map is a localized module map, i.e. the owner formulation of invertible `S`-action. -/
private theorem localizationModulesToLocalizedIdModules_obj_mem
    (M : ModuleCat (Localization S)) :
    localizedIdProperty S ((ModuleCat.restrictScalars (algebraMap R (Localization S))).obj M) := by
  let _ : Module R M := Module.compHom M (algebraMap R (Localization S))
  let _ : IsScalarTower R (Localization S) M := RestrictScalars.isScalarTower R (Localization S) M
  simpa using (isLocalizedModule_id S M (Localization S))

private noncomputable def localizationModulesToLocalizedIdModules :
    ModuleCat (Localization S) ⥤ (localizedIdProperty S).FullSubcategory :=
  (localizedIdProperty S).lift
    (ModuleCat.restrictScalars (algebraMap R (Localization S)))
    (localizationModulesToLocalizedIdModules_obj_mem S)

private noncomputable instance localizationModulesToLocalizedIdModules_faithful :
    (localizationModulesToLocalizedIdModules S).Faithful := by
  dsimp [localizationModulesToLocalizedIdModules]
  infer_instance

private noncomputable instance localizationModulesToLocalizedIdModules_full :
    (localizationModulesToLocalizedIdModules S).Full where
  map_surjective := by
    intro M N f
    let _ : Module R M := Module.compHom M (algebraMap R (Localization S))
    let _ : Module R N := Module.compHom N (algebraMap R (Localization S))
    let _ : IsScalarTower R (Localization S) M := RestrictScalars.isScalarTower R (Localization S) M
    let _ : IsScalarTower R (Localization S) N := RestrictScalars.isScalarTower R (Localization S) N
    refine ⟨ModuleCat.ofHom <|
      (show M →ₗ[R] N from f.hom.hom).extendScalarsOfIsLocalization S (Localization S), ?_⟩
    ext x
    rfl

private noncomputable instance localizationModulesToLocalizedIdModules_essSurj :
    (localizationModulesToLocalizedIdModules S).EssSurj where
  mem_essImage := by
    intro M
    letI : IsLocalizedModule S (LinearMap.id : M.obj →ₗ[R] M.obj) :=
      M.property
    letI : Module (Localization S) M.obj :=
      IsLocalizedModule.module S (LinearMap.id : M.obj →ₗ[R] M.obj)
    letI : IsScalarTower R (Localization S) M.obj :=
      IsLocalizedModule.isScalarTower_module S (LinearMap.id : M.obj →ₗ[R] M.obj)
    let hom :
        ((ModuleCat.restrictScalars (algebraMap R (Localization S))).obj
          (ModuleCat.of (Localization S) M.obj)) →ₗ[R] M.obj :=
      { toFun := fun x ↦ x
        map_add' := by intro x y; rfl
        map_smul' := by intro r x; simp }
    let inv :
        M.obj →ₗ[R]
          ((ModuleCat.restrictScalars (algebraMap R (Localization S))).obj
            (ModuleCat.of (Localization S) M.obj)) :=
      { toFun := fun x ↦ x
        map_add' := by intro x y; rfl
        map_smul' := by
          intro r x
          have h := (algebraMap_smul (Localization S) r x).symm
          convert h using 1 }
    refine ⟨ModuleCat.of (Localization S) M.obj, ?_⟩
    refine ⟨(localizedIdProperty S).isoMk ?_⟩
    refine
      { hom := show
            ((localizationModulesToLocalizedIdModules S).obj
              (ModuleCat.of (Localization S) M.obj)).obj ⟶ M.obj from
            ConcreteCategory.ofHom hom
        inv := show
            M.obj ⟶
              ((localizationModulesToLocalizedIdModules S).obj
                (ModuleCat.of (Localization S) M.obj)).obj from
            ConcreteCategory.ofHom inv }

private noncomputable instance :
    (localizationModulesToLocalizedIdModules S).IsEquivalence :=
  {}

private noncomputable def localizationModuleEquivalenceToLocalizedId :
    ModuleCat (Localization S) ≌ (localizedIdProperty S).FullSubcategory :=
  (localizationModulesToLocalizedIdModules S).asEquivalence

private noncomputable def localizedIdEquivInvertibleAction :
    (localizedIdProperty S).FullSubcategory ≌ (invertibleActionProperty S).FullSubcategory where
  functor :=
    (invertibleActionProperty S).lift ((localizedIdProperty S).ι) fun M ↦
      (localizedIdProperty_iff_invertibleAction S M.obj).1 M.property
  inverse :=
    (localizedIdProperty S).lift ((invertibleActionProperty S).ι) fun M ↦
      (localizedIdProperty_iff_invertibleAction S M.obj).2 M.property
  unitIso := Iso.refl _
  counitIso := Iso.refl _

/-- Lemma 10.9.5: the category of `S⁻¹R`-modules is equivalent to the full subcategory of
`R`-modules on which every element of `S` acts as an automorphism. -/
noncomputable def localizationModuleEquivalence :
    ModuleCat (Localization S) ≌
      ObjectProperty.FullSubcategory
        (fun M : ModuleCat R ↦ ∀ s : S, IsUnit (algebraMap R (Module.End R M) s)) :=
  (localizationModuleEquivalenceToLocalizedId S).trans (localizedIdEquivInvertibleAction S)

-- Proof sketch: the forward functor of `localizationModuleEquivalence` lands in the defining full
-- subcategory, so its image object carries the stated invertibility property by construction.
/-- The forward functor of `localizationModuleEquivalence` sends an `S⁻¹R`-module to an `R`-module
on which every element of `S` acts invertibly. -/
theorem localizationModuleEquivalence_functor_obj_isUnit
    (M : ModuleCat (Localization S)) (s : S) :
    IsUnit
      (algebraMap R
        (Module.End R ((localizationModuleEquivalence S).functor.obj M).obj) s) := sorry
