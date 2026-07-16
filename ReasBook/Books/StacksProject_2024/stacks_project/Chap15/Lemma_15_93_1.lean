import Mathlib
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
import StacksProject_2024.stacks_project.Chap04.Lemma_4_14_11
import StacksProject_2024.stacks_project.Chap10.Lemma_10_96_4
import StacksProject_2024.stacks_project.Chap12.Lemma_12_10_3
import StacksProject_2024.stacks_project.Chap15.Definition_15_65_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.ObjectProperty

universe u

noncomputable section

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory.DerivedCategory

section

variable {A : Type u} [CommRing A]

local notation "DMod" => DerivedCategory (ModuleCat A)

/-- Helper for Lemma 15.93.1: after restriction of scalars along `A → A_f`, every morphism from
an object of `D(A_f)` to `K` is zero. -/
def localizationAwayDerivedHomVanishingCondition (f : A) (K : DMod) : Prop :=
  ∀ E : DerivedCategory (ModuleCat (Localization.Away f)),
    Subsingleton
      (((ModuleCat.restrictScalars (algebraMap A (Localization.Away f))).mapDerivedCategory.obj E) ⟶
        K)

/-- Helper for Lemma 15.93.1: derived completeness in `D(A)` is the localization-away vanishing
condition for every `f ∈ I`. -/
def IsDerivedCompleteWithRespectTo (K : DMod) (I : Ideal A) : Prop :=
  ∀ f ∈ I, localizationAwayDerivedHomVanishingCondition f K

/-- Helper for Lemma 15.93.1: the chapter predicate on `D(A)` is already stated in pointwise
form. -/
theorem isDerivedCompleteWithRespectTo_iff
    (K : DMod) (I : Ideal A) :
    K.IsDerivedCompleteWithRespectTo I ↔
      ∀ f ∈ I, localizationAwayDerivedHomVanishingCondition f K :=
  Iff.rfl

/-- Helper for Lemma 15.93.1: the object property on `D(A)` selecting the derived-complete
objects with respect to `I`. -/
abbrev derivedCompleteObjectProperty (I : Ideal A) : ObjectProperty DMod :=
  fun K ↦ K.IsDerivedCompleteWithRespectTo I

end

end CategoryTheory.DerivedCategory

namespace ModuleCat

section

variable {A : Type u} [CommRing A]

/-- Helper for Lemma 15.93.1: a module is derived complete when its degree-zero object in `D(A)`
is derived complete. -/
abbrev IsDerivedCompleteWithRespectTo (M : ModuleCat A) (I : Ideal A) : Prop :=
  CategoryTheory.DerivedCategory.IsDerivedCompleteWithRespectTo
    (((ModuleCat.single0Functor : ModuleCat A ⥤ DerivedCategory (ModuleCat A)).obj M)) I

/-- Helper for Lemma 15.93.1: the object property on `Mod_A` selecting the derived-complete
modules with respect to `I`. -/
abbrev derivedCompleteObjectProperty (I : Ideal A) : ObjectProperty (ModuleCat A) :=
  fun M ↦ M.IsDerivedCompleteWithRespectTo I

/-- Lemma 15.93.1: the category `𝒞` of derived-complete `A`-modules with respect to `I` is the
full subcategory of `Mod_A` cut out by `ModuleCat.derivedCompleteObjectProperty I`. The later
abelian, limit, and adjoint properties are read from this owner category. -/
abbrev derivedCompleteModuleCat (I : Ideal A) :=
  (derivedCompleteObjectProperty I).FullSubcategory

end

end ModuleCat
