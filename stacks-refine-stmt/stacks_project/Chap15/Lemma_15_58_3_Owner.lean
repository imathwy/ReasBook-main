import Mathlib.Algebra.Category.ModuleCat.Biproducts
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
import Mathlib.Algebra.Homology.BifunctorHomotopy
import Mathlib.Algebra.Homology.Monoidal
import Mathlib.Algebra.Homology.Localization
import Mathlib.CategoryTheory.Localization.Monoidal.Braided
import Mathlib.CategoryTheory.Monoidal.Preadditive
import stacks_project.Chap13.Remark_13_10_9
import stacks_project.Chap15.Lemma_15_58_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open ComplexShape
open HomologicalComplex
open HomotopyCategory
open MonoidalCategory
open ModuleCat.MonoidalCategory

noncomputable section

set_option checkBinderAnnotations false

universe u

namespace CategoryTheory

section

variable {R : Type u} [CommRing R]

local notation "Complexes" => CochainComplex (ModuleCat R) ℤ
local notation "KMod" => HomotopyCategory (ModuleCat R) (up ℤ)
local notation "Qh" =>
  (HomotopyCategory.quotient (ModuleCat R) (up ℤ) : Complexes ⥤ KMod)
local notation "Qis" =>
  (HomologicalComplex.homotopyEquivalences (ModuleCat R) (up ℤ) :
    MorphismProperty Complexes)

private noncomputable abbrev homotopyQuotientUnitIso :
    (Qh : Complexes ⥤ KMod).obj (MonoidalCategoryStruct.tensorUnit Complexes) ≅
      (Qh : Complexes ⥤ KMod).obj (MonoidalCategoryStruct.tensorUnit Complexes) :=
  Iso.refl _

local instance : HasBinaryBiproducts (ModuleCat R) := inferInstance
local instance : SymmetricCategory Complexes := cochainComplexSymmetricCategory

private theorem homotopyEquivalences_isMonoidal :
    MorphismProperty.IsMonoidal (C := Complexes) Qis := by
  sorry

local instance : MorphismProperty.IsMonoidal (C := Complexes) Qis :=
  homotopyEquivalences_isMonoidal

local instance : Functor.IsLocalization Qh Qis :=
  (ComplexShape.up ℤ).quotient_isLocalization
    (fun n ↦ ⟨n - 1, by simp⟩)
    (ModuleCat R)

@[implicit_reducible] noncomputable instance homotopyCategory_moduleCat_monoidalCategory :
    MonoidalCategory KMod := by
  letI : MorphismProperty.IsMonoidal (C := Complexes) Qis :=
    homotopyEquivalences_isMonoidal
  change MonoidalCategory (LocalizedMonoidal Qh Qis homotopyQuotientUnitIso)
  infer_instance

@[implicit_reducible] noncomputable instance homotopyCategory_quotient_monoidal :
    (Qh : Complexes ⥤ KMod).Monoidal := by
  letI : MorphismProperty.IsMonoidal (C := Complexes) Qis :=
    homotopyEquivalences_isMonoidal
  simpa using
    (inferInstance :
      (Localization.Monoidal.toMonoidalCategory
        Qh
        Qis
        homotopyQuotientUnitIso).Monoidal)

@[implicit_reducible] noncomputable instance homotopyCategory_moduleCat_symmetric_category :
    SymmetricCategory KMod := by
  letI : MorphismProperty.IsMonoidal (C := Complexes) Qis :=
    homotopyEquivalences_isMonoidal
  let _ : MonoidalCategory KMod := homotopyCategory_moduleCat_monoidalCategory
  change SymmetricCategory (LocalizedMonoidal Qh Qis homotopyQuotientUnitIso)
  infer_instance

end

end CategoryTheory
