import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
import Mathlib.CategoryTheory.Sites.Monoidal

open CategoryTheory
open CategoryTheory.MonoidalCategory

noncomputable section

universe u v w

namespace CategoryTheory.Sheaf

section

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {Λ : Type w} [CommRing Λ]
variable [HasWeakSheafify J (ModuleCat.{w} Λ)]
variable [∀ U : C, HasWeakSheafify (J.over U) (ModuleCat.{w} Λ)]
variable [((J.W : MorphismProperty (Cᵒᵖ ⥤ ModuleCat.{w} Λ))).IsMonoidal]

/-- The canonical monoidal structure on sheaves of `Λ`-modules induced from the site-level
monoidal localization data. This is the reusable Chapter 21 owner behind the derived-tensor
surface on `DerivedCategory (Sheaf J (ModuleCat Λ))`. -/
instance moduleSheafMonoidalCategory :
    MonoidalCategory (Sheaf J (ModuleCat.{w} Λ)) :=
  Sheaf.monoidalCategory J (ModuleCat.{w} Λ)

end

end CategoryTheory.Sheaf

namespace SheafModuleDerivedTensor

open CategoryTheory.MonoidalCategory

/- Textbook surface notation for the derived tensor product object `K ⊗^L L` in a derived
category of sheaves of modules on a site, when the derived tensor is realized by the canonical
monoidal tensor on the ambient derived category. -/
scoped notation:70 K:70 " ⊗^L " L:71 => K ⊗ L

end SheafModuleDerivedTensor
