import Mathlib.Algebra.Category.ModuleCat.Biproducts
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
import Mathlib.Algebra.Homology.BifunctorHomotopy
import Mathlib.Algebra.Homology.Monoidal
import Mathlib.Algebra.Homology.Localization
import Mathlib.CategoryTheory.Localization.Monoidal.Braided
import Mathlib.CategoryTheory.Monoidal.Limits.Preserves
import Mathlib.CategoryTheory.Monoidal.Preadditive
import StacksProject_2024.stacks_project.Chap13.Remark_13_10_9
import StacksProject_2024.stacks_project.Chap15.Lemma_15_58_1

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open ComplexShape
open HomologicalComplex
open HomotopyCategory
open MonoidalCategory
noncomputable section

set_option checkBinderAnnotations false

universe u v

namespace CategoryTheory

section

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C]
variable [MonoidalCategory C] [SymmetricCategory C] [MonoidalPreadditive C] [HasColimits C]
variable [HasBinaryBiproducts C]
variable [(curriedTensor C).Additive]
variable [∀ X : C, ((curriedTensor C).obj X).Additive]
variable [∀ (K L : CochainComplex C ℤ), CochainComplex.HasMapBifunctor K L (curriedTensor C)]
variable [∀ G₁ G₂ : GradedObject ℤ C, GradedObject.HasTensor G₁ G₂]
variable [∀ G₁ G₂ G₃ : GradedObject ℤ C, GradedObject.HasGoodTensor₁₂Tensor G₁ G₂ G₃]
variable [∀ G₁ G₂ G₃ : GradedObject ℤ C, GradedObject.HasGoodTensorTensor₂₃ G₁ G₂ G₃]
variable [∀ G₁ G₂ G₃ G₄ : GradedObject ℤ C, GradedObject.HasTensor₄ObjExt G₁ G₂ G₃ G₄]
variable [∀ X : C, PreservesColimit (Functor.empty.{0} C) ((curriedTensor C).obj X)]
variable [∀ X : C, PreservesColimit (Functor.empty.{0} C) ((curriedTensor C).flip.obj X)]

local notation "Complexes" => CochainComplex C ℤ
local notation "KMod" => HomotopyCategory C (up ℤ)
local notation "Qh" =>
  (HomotopyCategory.quotient C (up ℤ) : Complexes ⥤ KMod)
local notation "Qis" =>
  (HomologicalComplex.homotopyEquivalences C (up ℤ) :
    MorphismProperty Complexes)

/-- Helper for Lemma 15.58.3: the quotient functor carries the tensor unit of complexes to the
same object of the homotopy category. -/
private noncomputable abbrev homotopyQuotientUnitIso :
    (Qh : Complexes ⥤ KMod).obj (MonoidalCategoryStruct.tensorUnit Complexes) ≅
      (Qh : Complexes ⥤ KMod).obj (MonoidalCategoryStruct.tensorUnit Complexes) :=
  Iso.refl _

local instance : SymmetricCategory Complexes := cochainComplexSymmetricCategory

/-- Helper for Lemma 15.58.3: tensoring on the left with a fixed complex preserves homotopy
equivalences. -/
private theorem homotopy_equivalences_whisker_left
    (X : Complexes) {Y₁ Y₂ : Complexes} (g : Y₁ ⟶ Y₂) (hg : Qis g) :
    Qis (X ◁ g) := by
  -- Unpack the homotopy-equivalence witness for `g`.
  rcases hg with ⟨e, rfl⟩
  refine ⟨HomotopyEquiv.mk (X ◁ e.hom) (X ◁ e.inv) ?_ ?_, rfl⟩
  · -- Transport the left inverse homotopy through the tensor bifunctor.
    let h₀ :
        Homotopy
          (HomologicalComplex.mapBifunctorMap
            (𝟙 X)
            (e.hom ≫ e.inv)
            (curriedTensor C)
            (up ℤ))
          (HomologicalComplex.mapBifunctorMap
            (𝟙 X)
            (𝟙 Y₁)
            (curriedTensor C)
            (up ℤ)) :=
      HomologicalComplex.mapBifunctorMapHomotopy₂
        (𝟙 X)
        e.homotopyHomInvId
        (curriedTensor C)
        (up ℤ)
    have h₁ : Homotopy (X ◁ (e.hom ≫ e.inv)) (X ◁ (𝟙 Y₁)) := by
      change Homotopy
        (HomologicalComplex.mapBifunctorMap
          (𝟙 X)
          (e.hom ≫ e.inv)
          (curriedTensor C)
          (up ℤ))
        (HomologicalComplex.mapBifunctorMap
          (𝟙 X)
          (𝟙 Y₁)
          (curriedTensor C)
          (up ℤ))
      exact h₀
    simpa only [MonoidalCategory.whiskerLeft_comp, MonoidalCategory.whiskerLeft_id] using h₁
  · -- Transport the right inverse homotopy through the tensor bifunctor.
    let h₀ :
        Homotopy
          (HomologicalComplex.mapBifunctorMap
            (𝟙 X)
            (e.inv ≫ e.hom)
            (curriedTensor C)
            (up ℤ))
          (HomologicalComplex.mapBifunctorMap
            (𝟙 X)
            (𝟙 Y₂)
            (curriedTensor C)
            (up ℤ)) :=
      HomologicalComplex.mapBifunctorMapHomotopy₂
        (𝟙 X)
        e.homotopyInvHomId
        (curriedTensor C)
        (up ℤ)
    have h₁ : Homotopy (X ◁ (e.inv ≫ e.hom)) (X ◁ (𝟙 Y₂)) := by
      change Homotopy
        (HomologicalComplex.mapBifunctorMap
          (𝟙 X)
          (e.inv ≫ e.hom)
          (curriedTensor C)
          (up ℤ))
        (HomologicalComplex.mapBifunctorMap
          (𝟙 X)
          (𝟙 Y₂)
          (curriedTensor C)
          (up ℤ))
      exact h₀
    simpa only [MonoidalCategory.whiskerLeft_comp, MonoidalCategory.whiskerLeft_id] using h₁

/-- Helper for Lemma 15.58.3: tensoring on the right with a fixed complex preserves homotopy
equivalences. -/
private theorem homotopy_equivalences_whisker_right
    {X₁ X₂ : Complexes} (f : X₁ ⟶ X₂) (hf : Qis f) (Y : Complexes) :
    Qis (f ▷ Y) := by
  -- Unpack the homotopy-equivalence witness for `f`.
  rcases hf with ⟨e, rfl⟩
  refine ⟨HomotopyEquiv.mk (e.hom ▷ Y) (e.inv ▷ Y) ?_ ?_, rfl⟩
  · -- Transport the left inverse homotopy through the tensor bifunctor.
    let h₀ :
        Homotopy
          (HomologicalComplex.mapBifunctorMap
            (e.hom ≫ e.inv)
            (𝟙 Y)
            (curriedTensor C)
            (up ℤ))
          (HomologicalComplex.mapBifunctorMap
            (𝟙 X₁)
            (𝟙 Y)
            (curriedTensor C)
            (up ℤ)) :=
      HomologicalComplex.mapBifunctorMapHomotopy₁
        e.homotopyHomInvId
        (𝟙 Y)
        (curriedTensor C)
        (up ℤ)
    have h₁ : Homotopy ((e.hom ≫ e.inv) ▷ Y) ((𝟙 X₁) ▷ Y) := by
      change Homotopy
        (HomologicalComplex.mapBifunctorMap
          (e.hom ≫ e.inv)
          (𝟙 Y)
          (curriedTensor C)
          (up ℤ))
        (HomologicalComplex.mapBifunctorMap
          (𝟙 X₁)
          (𝟙 Y)
          (curriedTensor C)
          (up ℤ))
      exact h₀
    simpa only [MonoidalCategory.comp_whiskerRight, MonoidalCategory.id_whiskerRight] using h₁
  · -- Transport the right inverse homotopy through the tensor bifunctor.
    let h₀ :
        Homotopy
          (HomologicalComplex.mapBifunctorMap
            (e.inv ≫ e.hom)
            (𝟙 Y)
            (curriedTensor C)
            (up ℤ))
          (HomologicalComplex.mapBifunctorMap
            (𝟙 X₂)
            (𝟙 Y)
            (curriedTensor C)
            (up ℤ)) :=
      HomologicalComplex.mapBifunctorMapHomotopy₁
        e.homotopyInvHomId
        (𝟙 Y)
        (curriedTensor C)
        (up ℤ)
    have h₁ : Homotopy ((e.inv ≫ e.hom) ▷ Y) ((𝟙 X₂) ▷ Y) := by
      change Homotopy
        (HomologicalComplex.mapBifunctorMap
          (e.inv ≫ e.hom)
          (𝟙 Y)
          (curriedTensor C)
          (up ℤ))
        (HomologicalComplex.mapBifunctorMap
          (𝟙 X₂)
          (𝟙 Y)
          (curriedTensor C)
          (up ℤ))
      exact h₀
    simpa only [MonoidalCategory.comp_whiskerRight, MonoidalCategory.id_whiskerRight] using h₁

/-- Helper for Lemma 15.58.3: homotopy equivalences contain identities and are stable under
composition. -/
private theorem homotopy_equivalences_is_multiplicative :
    MorphismProperty.IsMultiplicative (C := Complexes) Qis := by
  -- The identity map is witnessed by the trivial homotopy equivalence.
  letI : MorphismProperty.ContainsIdentities (C := Complexes) Qis :=
    ⟨fun X ↦ ⟨HomotopyEquiv.refl X, rfl⟩⟩
  -- Composition is witnessed by composing the underlying homotopy equivalences.
  letI : MorphismProperty.IsStableUnderComposition (C := Complexes) Qis :=
    ⟨fun f g hf hg ↦ by
      rcases hf with ⟨e₁, rfl⟩
      rcases hg with ⟨e₂, rfl⟩
      exact ⟨e₁.trans e₂, rfl⟩⟩
  exact MorphismProperty.IsMultiplicative.mk

/-- Lemma 15.58.3: the morphism property of homotopy equivalences on cochain complexes in `C` is
monoidal for the totalized tensor product. -/
private theorem homotopyEquivalences_isMonoidal :
    MorphismProperty.IsMonoidal (C := Complexes) Qis := by
  -- Route correction: prove monoidality on the chain level by showing that both left and right
  -- tensoring preserve homotopy equivalences, and then package these closures into the
  -- localization API.
  refine
    { toIsMultiplicative := homotopy_equivalences_is_multiplicative
      whiskerLeft := ?_
      whiskerRight := ?_ }
  · intro X Y₁ Y₂ g hg
    exact homotopy_equivalences_whisker_left X g hg
  · intro X₁ X₂ f hf Y
    exact homotopy_equivalences_whisker_right f hf Y

local instance : MorphismProperty.IsMonoidal (C := Complexes) Qis :=
  homotopyEquivalences_isMonoidal

local instance : Functor.IsLocalization Qh Qis :=
  (ComplexShape.up ℤ).quotient_isLocalization
    (fun n ↦ ⟨n - 1, by simp⟩)
    C

/-- Lemma 15.58.3: the homotopy category of complexes in `C` inherits the monoidal structure
induced by totalized tensor products. -/
@[implicit_reducible] noncomputable instance homotopyCategory_monoidalCategory :
    MonoidalCategory KMod := by
  -- The localization machinery packages the already-proved monoidality of homotopy equivalences.
  change MonoidalCategory (LocalizedMonoidal Qh Qis homotopyQuotientUnitIso)
  infer_instance

/-- Helper for Lemma 15.58.3: the quotient functor to the homotopy category is monoidal for the
localized tensor structure. -/
@[implicit_reducible] noncomputable instance homotopyCategory_quotient_monoidal :
    (Qh : Complexes ⥤ KMod).Monoidal := by
  -- This is the formal monoidal structure induced from the localized monoidal category.
  simpa using
    (inferInstance :
      (Localization.Monoidal.toMonoidalCategory
        Qh
        Qis
        homotopyQuotientUnitIso).Monoidal)

/-- Lemma 15.58.3: the homotopy category of complexes in `C` is symmetric monoidal. -/
@[implicit_reducible] noncomputable instance homotopyCategory_symmetricCategory :
    SymmetricCategory KMod := by
  -- The symmetric structure is the formal braided localization of the complex-level symmetry.
  change SymmetricCategory (LocalizedMonoidal Qh Qis homotopyQuotientUnitIso)
  infer_instance

end

end CategoryTheory
