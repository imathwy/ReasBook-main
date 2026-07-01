import Mathlib
import stacks_project.Chap06.Definition_6_26_1
import stacks_project.Chap06.Definition_6_31_2
import stacks_project.Chap06.Extension_by_zero_by_the_initial_object
import stacks_project.Chap06.Lemma_6_21_5
import stacks_project.Chap06.Restriction_and_extension_by_zero_for_module_valued_sheaves

open CategoryTheory
open CategoryTheory.Limits
open TopCat
open TopologicalSpace
open AlgebraicGeometry

noncomputable section

universe u

/- Domain-style sampling for Lemma 6.31.8:
- primary domain: extension by zero and restriction for sheaves of modules along the open
  immersion `j : U ↪ X` of a ringed space;
- sampled owner declarations:
  `openSubsetModulePresheafExtensionByZero`,
  `openSubsetModuleSheafExtensionByZero`,
  `moduleSheafRestrictionToOpen`,
  `moduleSheafExtensionByZeroAdjunction`;
- source/core/bridge triage:
  `source-facing`: the explicit open-immersion extension-by-zero functors on module presheaves and
  sheaves, together with the textbook unit and stalk statements;
  `core/canonical`: the restriction owner `moduleSheafRestrictionToOpen` and its chosen left
  adjoint `moduleSheafExtensionByZeroFromOpen`, packaged by
  `moduleSheafExtensionByZeroAdjunction`;
  `bridge/view`: the identification of the explicit source-facing extension-by-zero functors with
  the canonical adjoint owners, plus the resulting unit and stalk isomorphisms.

Primitive data are the open subset `U`, the ambient ringed space `X`, and the canonical module
extension/restriction functors already defined upstream. The only new public content here should be
the bridge from the explicit `j_!` construction to those owners and the source-facing stalk
consequences; one-off aliases for canonical owner expressions should be eliminated. -/

section

variable {X : RingedSpace.{u}} (U : Opens X.carrier)

private abbrev ambientModuleRingSheaf : X.carrier.Sheaf RingCat.{u} :=
  RingedSpace.ringCatSheaf X

private abbrev openSubspaceModuleRingSheaf : (extensionByZeroOpenSubsetSpace U).Sheaf RingCat.{u} :=
  (Sheaf.pullback RingCat.{u} (extensionByZeroOpenSubsetInclusion U)).obj ambientModuleRingSheaf

private instance :
    (openSubsetModulePresheafExtensionByZero U ambientModuleRingSheaf.presheaf).IsLeftAdjoint :=
  sorry

private theorem presheafModuleRestriction_eq_rightAdjoint :
    PresheafOfModules.pullback
        ((TopCat.Presheaf.pullbackPushforwardAdjunction RingCat.{u} U.inclusion').unit.app
          ambientModuleRingSheaf.presheaf) =
      (openSubsetModulePresheafExtensionByZero U ambientModuleRingSheaf.presheaf).rightAdjoint := by
  sorry

/-- Lemma 6.31.8 (1): the explicit extension-by-zero functor on presheaves of modules is left
adjoint to restriction to the open subset `U`. -/
noncomputable abbrev openSubsetModulePresheafExtensionByZeroAdjunction :
    openSubsetModulePresheafExtensionByZero U (RingedSpace.ringCatSheaf X).presheaf ⊣
      PresheafOfModules.pullback
        ((TopCat.Presheaf.pullbackPushforwardAdjunction RingCat.{u} U.inclusion').unit.app
          (RingedSpace.ringCatSheaf X).presheaf) :=
  (Adjunction.ofIsLeftAdjoint
      (openSubsetModulePresheafExtensionByZero U ambientModuleRingSheaf.presheaf)).ofNatIsoRight
    (eqToIso (presheafModuleRestriction_eq_rightAdjoint U).symm)

-- Proof sketch: extract the left-adjoint structure carried by the explicit adjunction.
/-- The presheaf extension-by-zero functor inherits its left-adjoint structure from the canonical
adjunction. -/
theorem openSubsetModulePresheafExtensionByZeroAdjunction_isLeftAdjoint :
    (openSubsetModulePresheafExtensionByZero U (RingedSpace.ringCatSheaf X).presheaf).IsLeftAdjoint
    := sorry

/-- The canonical extension-by-zero functor on presheaves of modules is a left adjoint. -/
instance :
    (openSubsetModulePresheafExtensionByZero U (RingedSpace.ringCatSheaf X).presheaf).IsLeftAdjoint :=
  openSubsetModulePresheafExtensionByZeroAdjunction_isLeftAdjoint U

-- Proof sketch: compare the explicit module-valued extension-by-zero construction with the
-- chosen left adjoint to restriction; they agree by uniqueness of left adjoints.
private theorem openSubsetModuleSheafExtensionByZero_eq_leftAdjoint :
    openSubsetModuleSheafExtensionByZero U ambientModuleRingSheaf =
      moduleSheafExtensionByZeroFromOpen U ambientModuleRingSheaf := by
  sorry

/-- The explicit source-facing extension-by-zero functor on sheaves of modules agrees with the
chapter’s canonical chosen left adjoint to restriction. -/
theorem openSubsetModuleSheafExtensionByZero_eq_moduleSheafExtensionByZeroFromOpen :
    openSubsetModuleSheafExtensionByZero U (RingedSpace.ringCatSheaf X) =
      moduleSheafExtensionByZeroFromOpen U (RingedSpace.ringCatSheaf X) := by
  simpa [ambientModuleRingSheaf] using openSubsetModuleSheafExtensionByZero_eq_leftAdjoint U

/-- Lemma 6.31.8 (2): the explicit extension-by-zero functor on sheaves of modules is left
adjoint to restriction to the open subset `U`. -/
noncomputable abbrev openSubsetModuleSheafExtensionByZeroAdjunction :
    openSubsetModuleSheafExtensionByZero U (RingedSpace.ringCatSheaf X) ⊣
      moduleSheafRestrictionToOpen U (RingedSpace.ringCatSheaf X) :=
  (moduleSheafExtensionByZeroAdjunction U ambientModuleRingSheaf).ofNatIsoLeft
    (eqToIso (openSubsetModuleSheafExtensionByZero_eq_moduleSheafExtensionByZeroFromOpen
      U).symm)

-- Proof sketch: extract the left-adjoint structure carried by the explicit sheaf adjunction.
/-- The sheaf extension-by-zero functor inherits its left-adjoint structure from the canonical
adjunction. -/
theorem openSubsetModuleSheafExtensionByZeroAdjunction_isLeftAdjoint :
    (openSubsetModuleSheafExtensionByZero U (RingedSpace.ringCatSheaf X)).IsLeftAdjoint := sorry

/-- The canonical extension-by-zero functor on sheaves of modules is a left adjoint. -/
instance :
    (openSubsetModuleSheafExtensionByZero U (RingedSpace.ringCatSheaf X)).IsLeftAdjoint :=
  openSubsetModuleSheafExtensionByZeroAdjunction_isLeftAdjoint U

-- Proof sketch: on the open subspace `U`, the unit of the sheaf-level adjunction restricts to the
-- identity on sections, so every unit component is an isomorphism.
private instance openSubspaceModuleSheafExtensionByZero_unit_app_isIso
    (ℱ : SheafOfModules (openSubspaceModuleRingSheaf U)) :
    IsIso ((openSubsetModuleSheafExtensionByZeroAdjunction U).unit.app ℱ) := sorry

/-- On sheaves of modules over `U`, the unit map
`\mathrm{id} \to j^{-1} j_!` is a natural isomorphism. -/
noncomputable abbrev openSubspaceModuleSheafExtensionByZero_unitIso :
    𝟭 (SheafOfModules
      ((Sheaf.pullback RingCat.{u} (extensionByZeroOpenSubsetInclusion U)).obj
        (RingedSpace.ringCatSheaf X))) ≅
      openSubsetModuleSheafExtensionByZero U (RingedSpace.ringCatSheaf X) ⋙
        moduleSheafRestrictionToOpen U (RingedSpace.ringCatSheaf X) :=
  NatIso.ofComponents
    (fun ℱ ↦ asIso ((openSubsetModuleSheafExtensionByZeroAdjunction U).unit.app ℱ))
    (fun φ ↦ by
      simpa using
        (openSubsetModuleSheafExtensionByZeroAdjunction U).unit.naturality φ)

-- Proof sketch: `openSubspaceModuleSheafExtensionByZero_unitIso` is assembled from the adjunction
-- unit by `NatIso.ofComponents`, so its hom component is exactly the unit morphism.
/-- The hom component of the unit isomorphism is the unit morphism of the sheaf adjunction. -/
theorem openSubspaceModuleSheafExtensionByZero_unitIso_hom_app
    (ℱ : SheafOfModules
      ((Sheaf.pullback RingCat.{u} (extensionByZeroOpenSubsetInclusion U)).obj
        (RingedSpace.ringCatSheaf X))) :
    (openSubspaceModuleSheafExtensionByZero_unitIso U).hom.app ℱ =
      (openSubsetModuleSheafExtensionByZeroAdjunction U).unit.app ℱ := sorry

-- Proof sketch: outside the open subset `U`, every sufficiently small neighborhood stays outside
-- `U`, so extension by zero contributes only the zero section module and the resulting stalk
-- vanishes.
/-- Lemma 6.31.8 (3), outside `U`: the module-valued stalk of `j_! ℱ` vanishes. -/
theorem openSubspaceModuleSheafExtensionByZero_stalk_isZero_of_not_mem
    (ℱ : SheafOfModules
      ((Sheaf.pullback RingCat.{u} (extensionByZeroOpenSubsetInclusion U)).obj
        (RingedSpace.ringCatSheaf X)))
    {x : X} (hx : x ∉ (U : Set X.carrier)) :
    IsZero (ModuleCat.of ((RingedSpace.ringCatSheaf X).presheaf.stalk x)
      ↑(Presheaf.stalk
        ((openSubsetModuleSheafExtensionByZero U (RingedSpace.ringCatSheaf X)).obj ℱ).val.presheaf
        x)) :=
  sorry

private abbrev openSubspaceModuleSheafExtensionByZeroRestricted
    (ℱ : SheafOfModules (openSubspaceModuleRingSheaf U)) :
    SheafOfModules (openSubspaceModuleRingSheaf U) :=
  (moduleSheafRestrictionToOpen U ambientModuleRingSheaf).obj
    ((openSubsetModuleSheafExtensionByZero U ambientModuleRingSheaf).obj ℱ)

private abbrev openSubspaceModuleSheafExtensionByZeroUnitPresheafMap
    (ℱ : SheafOfModules (openSubspaceModuleRingSheaf U)) :
    ℱ.val ⟶ (openSubspaceModuleSheafExtensionByZeroRestricted U ℱ).val :=
  ((openSubsetModuleSheafExtensionByZeroAdjunction U).unit.app ℱ).val

private abbrev openSubspaceModuleSheafExtensionByZeroUnitStalkMap
    (ℱ : SheafOfModules (openSubspaceModuleRingSheaf U)) (x : U) :
    Presheaf.stalk ℱ.val.presheaf x ⟶
      Presheaf.stalk (openSubspaceModuleSheafExtensionByZeroRestricted U ℱ).val.presheaf x := by
  simpa using
    (Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
      ((PresheafOfModules.toPresheaf _).map
        (openSubspaceModuleSheafExtensionByZeroUnitPresheafMap U ℱ))

private instance openSubspaceModuleSheafExtensionByZeroUnitStalkMap_isIso
    (ℱ : SheafOfModules (openSubspaceModuleRingSheaf U)) (x : U) :
    IsIso (openSubspaceModuleSheafExtensionByZeroUnitStalkMap U ℱ x) := by
  sorry

private theorem openSubspaceModuleSheafExtensionByZeroUnitStalkMap_smul
    (ℱ : SheafOfModules (openSubspaceModuleRingSheaf U)) (x : U)
    (r : ↑((openSubspaceModuleRingSheaf U).presheaf.stalk x))
    (m : ↑(Presheaf.stalk ℱ.val.presheaf x)) :
    openSubspaceModuleSheafExtensionByZeroUnitStalkMap U ℱ x (r • m) =
      r • openSubspaceModuleSheafExtensionByZeroUnitStalkMap U ℱ x m := by
  sorry

private abbrev openSubspaceModuleSheafStalk
    (ℱ : SheafOfModules (openSubspaceModuleRingSheaf U)) (x : U) :
    ModuleCat ((openSubspaceModuleRingSheaf U).presheaf.stalk x) :=
  ModuleCat.of ((openSubspaceModuleRingSheaf U).presheaf.stalk x)
    ↑(Presheaf.stalk ℱ.val.presheaf x)

private abbrev openSubspaceModuleSheafExtensionByZeroRestrictedStalk
    (ℱ : SheafOfModules (openSubspaceModuleRingSheaf U)) (x : U) :
    ModuleCat ((openSubspaceModuleRingSheaf U).presheaf.stalk x) :=
  ModuleCat.of ((openSubspaceModuleRingSheaf U).presheaf.stalk x)
    ↑(Presheaf.stalk (openSubspaceModuleSheafExtensionByZeroRestricted U ℱ).val.presheaf x)

private def openSubspaceModuleSheafExtensionByZeroUnitStalkHom
    (ℱ : SheafOfModules (openSubspaceModuleRingSheaf U)) (x : U) :
    openSubspaceModuleSheafStalk U ℱ x ⟶
      openSubspaceModuleSheafExtensionByZeroRestrictedStalk U ℱ x :=
  ModuleCat.homMk
    (openSubspaceModuleSheafExtensionByZeroUnitStalkMap U ℱ x)
    (fun r ↦ by
      ext m
      exact (openSubspaceModuleSheafExtensionByZeroUnitStalkMap_smul U ℱ x r m).symm)

private instance openSubspaceModuleSheafExtensionByZeroUnitStalkHom_isIso
    (ℱ : SheafOfModules (openSubspaceModuleRingSheaf U)) (x : U) :
    IsIso (openSubspaceModuleSheafExtensionByZeroUnitStalkHom U ℱ x) := by
  let F :=
    forget₂ (ModuleCat ((openSubspaceModuleRingSheaf U).presheaf.stalk x)) AddCommGrpCat
  have : IsIso (F.map (openSubspaceModuleSheafExtensionByZeroUnitStalkHom U ℱ x)) := by
    simpa [F, openSubspaceModuleSheafExtensionByZeroUnitStalkHom] using
      (openSubspaceModuleSheafExtensionByZeroUnitStalkMap_isIso U ℱ x)
  exact isIso_of_reflects_iso (openSubspaceModuleSheafExtensionByZeroUnitStalkHom U ℱ x) F

private noncomputable abbrev openSubspaceModuleSheafExtensionByZero_restrictedStalkIso
    (ℱ : SheafOfModules (openSubspaceModuleRingSheaf U))
    (x : U) :
    ModuleCat.of
        (((Sheaf.pullback RingCat.{u} (extensionByZeroOpenSubsetInclusion U)).obj
            (RingedSpace.ringCatSheaf X)).presheaf.stalk x)
        ↑(Presheaf.stalk
          ((moduleSheafRestrictionToOpen U (RingedSpace.ringCatSheaf X)).obj
            ((openSubsetModuleSheafExtensionByZero U (RingedSpace.ringCatSheaf X)).obj ℱ)).val.presheaf
          x) ≅
      ModuleCat.of
        (((Sheaf.pullback RingCat.{u} (extensionByZeroOpenSubsetInclusion U)).obj
            (RingedSpace.ringCatSheaf X)).presheaf.stalk x)
        ↑(Presheaf.stalk ℱ.val.presheaf x) := by
  simpa [ambientModuleRingSheaf, openSubspaceModuleRingSheaf,
    openSubspaceModuleSheafExtensionByZeroRestricted, openSubspaceModuleSheafStalk,
    openSubspaceModuleSheafExtensionByZeroRestrictedStalk] using
    (asIso (openSubspaceModuleSheafExtensionByZeroUnitStalkHom U ℱ x)).symm

private abbrev openSubspaceModuleSheafExtensionByZeroAmbientStalk
    (ℱ : SheafOfModules (openSubspaceModuleRingSheaf U)) (x : U) :
    ModuleCat ((openSubspaceModuleRingSheaf U).presheaf.stalk x) :=
  let M :
      ModuleCat (ambientModuleRingSheaf.presheaf.stalk (extensionByZeroOpenSubsetInclusion U x)) :=
    ModuleCat.of
      (ambientModuleRingSheaf.presheaf.stalk (extensionByZeroOpenSubsetInclusion U x))
      ↑(Presheaf.stalk
        ((openSubsetModuleSheafExtensionByZero U ambientModuleRingSheaf).obj ℱ).val.presheaf
        (extensionByZeroOpenSubsetInclusion U x))
  (ModuleCat.restrictScalars
      (((TopCat.Sheaf.stalkPullbackIso
          (extensionByZeroOpenSubsetInclusion U) ambientModuleRingSheaf x).symm).hom.hom)).obj M

private theorem openSubspaceModuleSheafExtensionByZeroAmbientStalk_eq
    (ℱ : SheafOfModules (openSubspaceModuleRingSheaf U)) (x : U) :
    openSubspaceModuleSheafExtensionByZeroRestrictedStalk U ℱ x =
      openSubspaceModuleSheafExtensionByZeroAmbientStalk U ℱ x := by
  sorry

private noncomputable abbrev openSubspaceModuleSheafExtensionByZeroAmbientStalkIso
    (ℱ : SheafOfModules (openSubspaceModuleRingSheaf U)) (x : U) :
    openSubspaceModuleSheafExtensionByZeroRestrictedStalk U ℱ x ≅
      openSubspaceModuleSheafExtensionByZeroAmbientStalk U ℱ x :=
  eqToIso (openSubspaceModuleSheafExtensionByZeroAmbientStalk_eq U ℱ x)

/-- Lemma 6.31.8 (3), on `U`: for `x : U`, the stalk of `j_! \mathcal{F}` at the corresponding
point of `X` is canonically isomorphic to the stalk of `\mathcal{F}` at `x`. The left-hand side
is viewed as an `\mathcal{O}_{U, x}`-module via the canonical stalk isomorphism
`\mathcal{O}_{U, x} \cong \mathcal{O}_{X, x}` coming from pullback along the open immersion. -/
noncomputable abbrev openSubspaceModuleSheafExtensionByZero_stalkIso
    (ℱ : SheafOfModules
      ((Sheaf.pullback RingCat.{u} (extensionByZeroOpenSubsetInclusion U)).obj
        (RingedSpace.ringCatSheaf X)))
    (x : U) :
      (ModuleCat.restrictScalars
        (((TopCat.Sheaf.stalkPullbackIso
            (extensionByZeroOpenSubsetInclusion U) (RingedSpace.ringCatSheaf X) x).symm).hom.hom)).obj
      (ModuleCat.of
        ((RingedSpace.ringCatSheaf X).presheaf.stalk (extensionByZeroOpenSubsetInclusion U x))
        ↑(Presheaf.stalk
          ((openSubsetModuleSheafExtensionByZero U (RingedSpace.ringCatSheaf X)).obj ℱ).val.presheaf
          (extensionByZeroOpenSubsetInclusion U x))) ≅
      ModuleCat.of
        (((Sheaf.pullback RingCat.{u} (extensionByZeroOpenSubsetInclusion U)).obj
            (RingedSpace.ringCatSheaf X)).presheaf.stalk x)
        ↑(Presheaf.stalk ℱ.val.presheaf x) := by
  simpa [ambientModuleRingSheaf, openSubspaceModuleRingSheaf,
    openSubspaceModuleSheafExtensionByZeroAmbientStalk] using
    (openSubspaceModuleSheafExtensionByZeroAmbientStalkIso U ℱ x).symm ≪≫
      openSubspaceModuleSheafExtensionByZero_restrictedStalkIso U ℱ x

end
