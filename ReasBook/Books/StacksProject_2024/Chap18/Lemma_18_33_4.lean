import Mathlib
import stacks_project.Chap18.Definition_18_28_1
import stacks_project.Chap18.Lemma_18_33_2

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open PresheafOfModules.DifferentialsConstruction
open scoped SheafOfModules.RingedSite

noncomputable section

universe u v

/- Domain-style sampling for Lemma 18.33.4:
- primary domain: sheafification of presheaves of modules over a presheaf of commutative rings,
  applied to the canonical presheaf of relative differentials;
- sampled owner declarations:
  `PresheafOfModules.commRingSheafification`,
  `PresheafOfModules.moduleSheafification`,
  `SheafOfModules.RingedSite.relativeDifferentials`;
- best owner abstraction: the presheaf-side module sheafification functor
  `PresheafOfModules.moduleSheafification` and the sheaf-side relative-differentials owner `Ω(φ)`;
- primitive data: a morphism `φ : O₁ ⟶ O₂` of presheaves of commutative rings and its sheafified
  morphism `(presheafToSheaf J CommRingCat).map φ`;
- derived API: the canonical comparison isomorphism identifying the sheafification of the
  presheaf-level relative differentials with the relative-differentials sheaf of the sheafified
  morphism.

Source/core/bridge triage:
- `core/canonical`: `PresheafOfModules.moduleSheafification` and
  `SheafOfModules.RingedSite.relativeDifferentials`;
- `bridge/view`: the comparison isomorphism in this file.

This item is therefore a bridge theorem. The local wrapper definitions previously duplicating the
chapter owners are removed in favor of those canonical declarations. -/

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
variable [HasWeakSheafify J CommRingCat.{max u v}]
variable [J.WEqualsLocallyBijective CommRingCat.{max u v}]
variable [HasWeakSheafify J AddCommGrpCat.{max u v}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable (O₁ O₂ : Cᵒᵖ ⥤ CommRingCat.{max u v})
variable (φ : O₁ ⟶ O₂)

omit [J.WEqualsLocallyBijective CommRingCat.{max u v}]
  [HasWeakSheafify J AddCommGrpCat.{max u v}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}] in
/-- The sectionwise commutativity relation comparing `φ` with its sheafification. -/
private theorem sheafifiedRelativeDifferentialsSquare_app (X : Cᵒᵖ) :
    (CategoryTheory.toSheafify J O₁).app X ≫
        ((presheafToSheaf J CommRingCat.{max u v}).map φ).hom.app X =
      φ.app X ≫ (CategoryTheory.toSheafify J O₂).app X := by
  exact congrArg (fun k ↦ k.app X) (CategoryTheory.toSheafify_naturality J φ).symm

/-- The objectwise comparison on Kähler differentials induced by sheafification. -/
private abbrev sheafifiedRelativeDifferentialsMapApp (X : Cᵒᵖ) :
    (relativeDifferentials' φ).obj X ⟶
      ((PresheafOfModules.restrictScalars
          (PresheafOfModules.sheafificationRingMap J O₂)).obj
        (relativeDifferentials'
          ((presheafToSheaf J CommRingCat.{max u v}).map φ).hom)).obj X :=
  CommRingCat.KaehlerDifferential.map
    (sheafifiedRelativeDifferentialsSquare_app J O₁ O₂ φ X)

-- Proof sketch: both sides are morphisms out of the objectwise Kähler differentials on `O₂(X)`.
-- Equality on generators `d b` reduces to the naturality of `toSheafify` together with
-- `CommRingCat.KaehlerDifferential.map_d`.
/-- The objectwise sheafification comparison on relative differentials is natural in the site
variable. -/
private theorem sheafifiedRelativeDifferentialsMapApp_naturality
    {X Y : Cᵒᵖ} (f : X ⟶ Y) :
    (relativeDifferentials' φ).map f ≫
        (ModuleCat.restrictScalars
            (((O₂ ⋙ forget₂ CommRingCat RingCat).map f).hom)).map
          (sheafifiedRelativeDifferentialsMapApp J O₁ O₂ φ Y) =
      sheafifiedRelativeDifferentialsMapApp J O₁ O₂ φ X ≫
        ((PresheafOfModules.restrictScalars
            (PresheafOfModules.sheafificationRingMap J O₂)).obj
          (relativeDifferentials'
            ((presheafToSheaf J CommRingCat.{max u v}).map φ).hom)).map f := sorry

/-- The presheaf-level comparison on relative differentials induced by sheafifying `φ`. -/
private noncomputable def sheafifiedRelativeDifferentialsMapPresheaf :
    relativeDifferentials' φ ⟶
      (PresheafOfModules.restrictScalars
          (PresheafOfModules.sheafificationRingMap J O₂)).obj
        (relativeDifferentials'
          ((presheafToSheaf J CommRingCat.{max u v}).map φ).hom) where
  app X := sheafifiedRelativeDifferentialsMapApp J O₁ O₂ φ X
  naturality f := sheafifiedRelativeDifferentialsMapApp_naturality J O₁ O₂ φ f

-- Proof sketch: descend the presheaf comparison map through the module-sheafification adjunction,
-- then use the sheafification unit for the sheaf-level owner `Ω(O₁^# ⟶ O₂^#)`.
/-- The canonical comparison morphism from the sheafification of the presheaf-level relative
differentials to the sheaf of relative differentials of the sheafified morphism. -/
noncomputable def moduleSheafification_relativeDifferentials_comparison :
    (PresheafOfModules.moduleSheafification J O₂).obj (relativeDifferentials' φ) ⟶
      Ω((presheafToSheaf J CommRingCat.{max u v}).map φ) :=
  ((PresheafOfModules.sheafificationAdjunction
      (PresheafOfModules.sheafificationRingMap J O₂)).homEquiv
    (relativeDifferentials' φ)
    (Ω((presheafToSheaf J CommRingCat.{max u v}).map φ))).symm
    (sheafifiedRelativeDifferentialsMapPresheaf J O₁ O₂ φ ≫
      (PresheafOfModules.restrictScalars
          (PresheafOfModules.sheafificationRingMap J O₂)).map
        ((PresheafOfModules.sheafificationAdjunction
            (𝟙
              (ringSheaf J (PresheafOfModules.commRingSheafification J O₂)).obj)).unit.app
          (relativeDifferentials'
            ((presheafToSheaf J CommRingCat.{max u v}).map φ).hom)))

-- Proof sketch: both sides are obtained by sheafifying the objectwise cokernel presentation of
-- Kähler differentials from `18.33.2.1`. Exactness of module sheafification identifies the
-- resulting presentations, and hence the comparison morphism is an isomorphism.
/-- The canonical comparison morphism of Lemma 18.33.4 is an isomorphism. -/
instance moduleSheafification_relativeDifferentials_comparison_isIso :
    IsIso (moduleSheafification_relativeDifferentials_comparison J O₁ O₂ φ) := by
  sorry

/-- Lemma 18.33.4: for a morphism `φ : O₁ ⟶ O₂` of presheaves of commutative rings on a site, the
sheaf of relative differentials of the sheafified morphism `O₁^# ⟶ O₂^#` is canonically
isomorphic to the module sheafification of the presheaf `U ↦ Ω[O₂(U)⁄O₁(U)]`. -/
noncomputable abbrev moduleSheafification_relativeDifferentials_iso :
    (PresheafOfModules.moduleSheafification J O₂).obj (relativeDifferentials' φ) ≅
      Ω((presheafToSheaf J CommRingCat.{max u v}).map φ) :=
  asIso (moduleSheafification_relativeDifferentials_comparison J O₁ O₂ φ)
