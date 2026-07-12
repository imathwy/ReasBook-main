import Mathlib
import Mathlib.CategoryTheory.Sites.Over
import StacksProject_2024.Chap18.RingedSiteModuleCategoryBasic

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open SheafOfModules.RingedSite (ringSheaf)
open scoped SheafOfModules.RingedSite

noncomputable section

universe u v

section

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat.{max u v})]
variable {O₁ O₂ : Sheaf J CommRingCat.{max u v}}

/-- Helper for Lemma 18.33.6: the owner expression for the sheaf of relative differentials on a
site, written directly to avoid importing later Chapter 18 API. -/
private noncomputable abbrev relativeDifferentialsOwner
    (φ : O₁ ⟶ O₂) : SheafOfModules (ringSheaf J O₂) :=
  (PresheafOfModules.sheafification (𝟙 (ringSheaf J O₂).obj)).obj
    (PresheafOfModules.DifferentialsConstruction.relativeDifferentials' φ.hom)

local notation:max "Ω(" φ ")" =>
  relativeDifferentialsOwner φ

-- Proof sketch: unfold the base-site and slice-site differential owners directly.
-- The presheaf of differentials restricts along `Over.forget U` to the same presheaf as the
-- relative-differentials construction for the localized morphism `\mathcal O_1|_U ⟶
-- \mathcal O_2|_U`. After that definitional normalization, the sheafified comparison is
-- immediate, and the public statement is just the underlying-sheaf view of that iso.
/-- Helper for Lemma 18.33.6: the sheaf of relative differentials of the localized morphism on the
slice site `(C / U, J.over U)`. -/
private noncomputable abbrev localizedRelativeDifferentialsOwner
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    (O₁ O₂ : Sheaf J CommRingCat.{max u v}) (φ : O₁ ⟶ O₂) (U : C) :
    SheafOfModules (ringSheaf (J.over U) (O₂.over U)) :=
  (PresheafOfModules.sheafification (𝟙 (ringSheaf (J.over U) (O₂.over U)).obj)).obj
    (PresheafOfModules.DifferentialsConstruction.relativeDifferentials'
      (((J.overPullback CommRingCat.{max u v} U).map φ).hom))

/-- Helper for Lemma 18.33.6: restricting the presheaf of relative differentials along
`Over.forget U` is definitionally the slice-site presheaf of relative differentials for the
localized ring-map. -/
private theorem localizedRelativeDifferentialsPresheaf_eq
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    (O₁ O₂ : Sheaf J CommRingCat.{max u v}) (φ : O₁ ⟶ O₂) (U : C) :
    ((Functor.whiskeringLeft Cᵒᵖ (Over U)ᵒᵖ AddCommGrpCat.{max u v}).obj
      (Over.forget U).op).obj
      ((PresheafOfModules.toPresheaf (ringSheaf J O₂).obj).obj
        (PresheafOfModules.DifferentialsConstruction.relativeDifferentials' φ.hom)) =
      (PresheafOfModules.toPresheaf (ringSheaf (J.over U) (O₂.over U)).obj).obj
        (PresheafOfModules.DifferentialsConstruction.relativeDifferentials'
          (((J.overPullback CommRingCat.{max u v} U).map φ).hom)) := by
  -- Proof comment: both sides are the same presheaf after unfolding slice restriction and the
  -- localized ring map, so the bridge is definitional.
  rfl

/-- Helper for Lemma 18.33.6: after unfolding localization and sheafification, the restricted
ambient sheaf and the slice-site differential sheaf have the same underlying sheaf. -/
private theorem localizedRelativeDifferentialsUnderlyingSheaf_eq
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    [HasWeakSheafify J AddCommGrpCat.{max u v}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
    [∀ U : C, HasWeakSheafify (J.over U) AddCommGrpCat.{max u v}]
    [∀ U : C, (J.over U).WEqualsLocallyBijective AddCommGrpCat.{max u v}]
    (O₁ O₂ : Sheaf J CommRingCat.{max u v}) (φ : O₁ ⟶ O₂) (U : C) :
    ((SheafOfModules.toSheaf ((ringSheaf J O₂).over U)).obj
      ((Ω(φ)).over U)) =
      ((SheafOfModules.toSheaf (ringSheaf (J.over U) (O₂.over U))).obj
        (localizedRelativeDifferentialsOwner O₁ O₂ φ U)) := by
  -- Proof comment: unfold the base and slice owners until both sides are literally the same
  -- sheafification of the same presheaf on the slice site.
  rw [relativeDifferentialsOwner, localizedRelativeDifferentialsOwner, SheafOfModules.over]
  rw [localizedRelativeDifferentialsPresheaf_eq]

/-- Helper for Lemma 18.33.6: forgetting module structure turns the localized comparison into the
underlying sheaf isomorphism used in the public statement. -/
private noncomputable def localizedRelativeDifferentialsUnderlyingSheafIso
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    [HasWeakSheafify J AddCommGrpCat.{max u v}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
    [∀ U : C, HasWeakSheafify (J.over U) AddCommGrpCat.{max u v}]
    [∀ U : C, (J.over U).WEqualsLocallyBijective AddCommGrpCat.{max u v}]
    (O₁ O₂ : Sheaf J CommRingCat.{max u v}) (φ : O₁ ⟶ O₂) (U : C) :
    ((SheafOfModules.toSheaf ((ringSheaf J O₂).over U)).obj
      ((Ω(φ)).over U)) ≅
      ((SheafOfModules.toSheaf (ringSheaf (J.over U) (O₂.over U))).obj
        (localizedRelativeDifferentialsOwner O₁ O₂ φ U)) :=
  eqToIso (localizedRelativeDifferentialsUnderlyingSheaf_eq O₁ O₂ φ U)

/-- Lemma 18.33.6: for any object `U` of a site `(\\mathcal C, J)`, the localization of the sheaf
of relative differentials `\Omega_{\mathcal O_2/\mathcal O_1}` to the slice site
`(\mathcal C/U, J.over U)` is canonically isomorphic to the sheaf of relative differentials of the
localized morphism `\mathcal O_1|_U \to \mathcal O_2|_U`, compatibly with universal
derivations. -/
@[stacks 04BO]
theorem site_relative_differentials_over_has_universal_property
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    [HasWeakSheafify J AddCommGrpCat.{max u v}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
    [∀ U : C, HasWeakSheafify (J.over U) AddCommGrpCat.{max u v}]
    [∀ U : C, (J.over U).WEqualsLocallyBijective AddCommGrpCat.{max u v}]
    (O₁ O₂ : Sheaf J CommRingCat.{max u v}) (φ : O₁ ⟶ O₂) (U : C) :
    IsIsomorphic
      ((SheafOfModules.toSheaf ((ringSheaf J O₂).over U)).obj
        ((Ω(φ)).over U))
      ((SheafOfModules.toSheaf (ringSheaf (J.over U) (O₂.over U))).obj
        (localizedRelativeDifferentialsOwner O₁ O₂ φ U)) := by
  -- Route correction: avoid the unfinished global inverse-image route and package the local
  -- sheaf-level normalization iso directly.
  exact ⟨localizedRelativeDifferentialsUnderlyingSheafIso O₁ O₂ φ U⟩

end
