import Mathlib.CategoryTheory.ObjectProperty.Basic
import StacksProject_2024.Chap21.Lemma_21_28_1
import StacksProject_2024.Chap21.Definition_21_43_1

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory Opposite
open CategoryTheory.ObjectProperty

universe u v

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory.ModulesOnCategory

section

variable {D : Type u} [Category D]
variable {E : Type v} [Category E]

/-
Domain-style sampling for Lemma 21.43.5:
- primary domain: Hom-set equivalences obtained from an adjunction and a counit isomorphism on a
  chosen object;
- sampled owner declarations:
  `Adjunction.homEquiv`,
  `Iso.homCongr`,
  `CategoryTheory.counitIsomorphismProperty`;
- best owner abstraction:
  `source-facing`: the Section `21.43` specialization with `K ∈ QC(𝒞, 𝒪)`;
  `core/canonical`: an ambient object `K : D` together with the repository-canonical predicate
    `counitIsomorphismProperty Lf RGamma adj K`;
  `bridge/view`: transport of `Adjunction.homEquiv` along the counit isomorphism via
    `Iso.homCongr`.
- primitive data: an adjunction `Lf ⊣ RGamma`, an object `K : D`, the fact that the counit map on
  `K` is an isomorphism, and a target object `M`;
- derived API: the canonical equivalence
  `(K ⟶ M) ≃ (RGamma.obj K ⟶ RGamma.obj M)`.

Source/core/bridge triage:
- `source-facing`: the `QC` specialization used in Section `21.43`;
- `core/canonical`: the counit-isomorphism predicate on an ambient object;
- `bridge/view`: `Adjunction.homEquiv` transported by `Iso.homCongr`, together with the reusable
  full-subcategory specialization below.
-/

/-- Ambient counit-isomorphism bridge used by Lemma `21.43.5`: if the counit map
`Lf.obj (RGamma.obj K) ⟶ K` of an adjunction `Lf ⊣ RGamma` is an isomorphism, then morphisms
`K ⟶ M` are canonically equivalent to morphisms `RGamma.obj K ⟶ RGamma.obj M`. The Stacks-tagged
source-facing entry is the `QC` specialization `sections_homEquivOfQC`; the full-subcategory form
below is the reusable bridge layer. -/
noncomputable abbrev sections_homEquiv
    (RGamma : D ⥤ E) (Lf : E ⥤ D) (adj : Lf ⊣ RGamma)
    (K : D) (hcounit : counitIsomorphismProperty Lf RGamma adj K) (M : D) :
    (K ⟶ M) ≃ (RGamma.obj K ⟶ RGamma.obj M) :=
  let _ : IsIso (adj.counit.app K) := hcounit
  (Iso.homCongr (asIso (adj.counit.app K)).symm (Iso.refl M)).trans
    (adj.homEquiv (RGamma.obj K) M)

/-- The forward map of `sections_homEquiv` is the adjunction bijection applied to
`adj.counit.app K ≫ f`. -/
@[simp] theorem sections_homEquiv_apply
    (RGamma : D ⥤ E) (Lf : E ⥤ D) (adj : Lf ⊣ RGamma)
    (K : D) (hcounit : counitIsomorphismProperty Lf RGamma adj K) (M : D) (f : K ⟶ M) :
    sections_homEquiv RGamma Lf adj K hcounit M f =
      adj.homEquiv (RGamma.obj K) M ((adj.counit.app K) ≫ f) := by
  change (adj.homEquiv (RGamma.obj K) M)
      (((asIso (adj.counit.app K)).symm).inv ≫ f ≫ (Iso.refl M).hom) = _
  simp

/-- The inverse map of `sections_homEquiv` is obtained by first using the inverse adjunction
equivalence and then precomposing with the inverse counit isomorphism. -/
@[simp] theorem sections_homEquiv_symm_apply
    (RGamma : D ⥤ E) (Lf : E ⥤ D) (adj : Lf ⊣ RGamma)
    (K : D) (hcounit : counitIsomorphismProperty Lf RGamma adj K) (M : D)
    (g : RGamma.obj K ⟶ RGamma.obj M) :
    (sections_homEquiv RGamma Lf adj K hcounit M).symm g =
      (asIso (adj.counit.app K)).inv ≫ ((adj.homEquiv (RGamma.obj K) M).symm g) := by
  change ((asIso (adj.counit.app K)).symm).hom ≫ ((adj.homEquiv (RGamma.obj K) M).symm g) ≫
      (Iso.refl M).inv = _
  simp

/-- Reusable full-subcategory specialization of `sections_homEquiv`: if every object of `P`
satisfies the counit-isomorphism property for `Lf ⊣ RGamma`, then morphisms `K.obj ⟶ M` are
canonically equivalent to morphisms `RGamma.obj K.obj ⟶ RGamma.obj M`. The Stacks-facing
Section `21.43` declaration is the `QC` specialization `sections_homEquivOfQC` below. -/
noncomputable abbrev sections_homEquivOfFullSubcategory
    (RGamma : D ⥤ E) (Lf : E ⥤ D) (adj : Lf ⊣ RGamma)
    (P : ObjectProperty D)
    (hP : P ≤ counitIsomorphismProperty Lf RGamma adj)
    (K : P.FullSubcategory) (M : D) :
    (K.obj ⟶ M) ≃ (RGamma.obj K.obj ⟶ RGamma.obj M) :=
  sections_homEquiv RGamma Lf adj K.obj (hP K.obj K.property) M

/-- The forward map of `sections_homEquivOfFullSubcategory` is the ambient counit-isomorphism
bridge specialized to `K.obj`. -/
@[simp] theorem sections_homEquivOfFullSubcategory_apply
    (RGamma : D ⥤ E) (Lf : E ⥤ D) (adj : Lf ⊣ RGamma)
    (P : ObjectProperty D)
    (hP : P ≤ counitIsomorphismProperty Lf RGamma adj)
    (K : P.FullSubcategory) (M : D) (f : K.obj ⟶ M) :
    sections_homEquivOfFullSubcategory RGamma Lf adj P hP K M f =
      adj.homEquiv (RGamma.obj K.obj) M ((adj.counit.app K.obj) ≫ f) := by
  simpa [sections_homEquivOfFullSubcategory] using
    sections_homEquiv_apply RGamma Lf adj K.obj (hP K.obj K.property) M f

end

section

variable {C : Type u} [Category C]
variable {D : Type v} [Category D]
variable (𝒪 : Cᵒᵖ ⥤ CommRingCat.{u})
variable (RGamma : ∀ U : C, D ⥤ DerivedCategory (ModuleCat (𝒪.obj (op U))))
variable
  (derivedRestrict :
    ∀ {U V : C},
      (U ⟶ V) →
      DerivedCategory (ModuleCat (𝒪.obj (op V))) ⥤
        DerivedCategory (ModuleCat (𝒪.obj (op U))))
variable
  (comparison :
    ∀ {U V : C} (f : U ⟶ V),
      RGamma V ⋙ derivedRestrict f ⟶ RGamma U)
variable (X : C)

/-- Lemma 21.43.5: for the Section `21.43` quasi-coherent full subcategory `QC(𝒞, 𝒪)`, if the
adjunction counit of `Lf ⊣ RΓ(X, -)` is an isomorphism on every quasi-coherent object, then
morphisms `K ⟶ M` are canonically equivalent to morphisms `RΓ(X, K) ⟶ RΓ(X, M)`. This is the
source-facing `QC` specialization of the ambient bridge `sections_homEquiv`. -/
@[stacks 0H0S]
noncomputable abbrev sections_homEquivOfQC
    (Lf : DerivedCategory (ModuleCat (𝒪.obj (op X))) ⥤ D)
    (adj : Lf ⊣ RGamma X)
    (hQC :
      isQuasiCoherent 𝒪 RGamma derivedRestrict comparison ≤
        counitIsomorphismProperty Lf (RGamma X) adj)
    (K : QC 𝒪 RGamma derivedRestrict comparison) (M : D) :
    (K.obj ⟶ M) ≃ ((RGamma X).obj K.obj ⟶ (RGamma X).obj M) :=
  sections_homEquivOfFullSubcategory
    (RGamma X) Lf adj (isQuasiCoherent 𝒪 RGamma derivedRestrict comparison) hQC K M

/-- The forward map of `sections_homEquivOfQC` is the adjunction bijection applied to
`adj.counit.app K.obj ≫ f`. -/
@[simp] theorem sections_homEquivOfQC_apply
    (Lf : DerivedCategory (ModuleCat (𝒪.obj (op X))) ⥤ D)
    (adj : Lf ⊣ RGamma X)
    (hQC :
      isQuasiCoherent 𝒪 RGamma derivedRestrict comparison ≤
        counitIsomorphismProperty Lf (RGamma X) adj)
    (K : QC 𝒪 RGamma derivedRestrict comparison) (M : D) (f : K.obj ⟶ M) :
    sections_homEquivOfQC 𝒪 RGamma derivedRestrict comparison X Lf adj hQC K M f =
      adj.homEquiv ((RGamma X).obj K.obj) M ((adj.counit.app K.obj) ≫ f) := by
  simpa [sections_homEquivOfQC] using
    sections_homEquivOfFullSubcategory_apply
      ((RGamma X)) Lf adj (isQuasiCoherent 𝒪 RGamma derivedRestrict comparison) hQC K M f

end

end CategoryTheory.ModulesOnCategory
