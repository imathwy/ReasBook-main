import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.CategoryTheory.Abelian.FunctorCategory
import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import StacksProject_2024.stacks_project.Chap13.Situation_13_15_1

open CategoryTheory
open CategoryTheory.Limits
open ComplexShape
open scoped CategoryTheory

noncomputable section

attribute [local instance] HasDerivedCategory.standard

universe u v w

namespace CategoryTheory

section Derived

/-- The colimit functor on `A`-valued presheaves over `C` is additive. This supplies the canonical
Chapter 13 owner input used to form `categoryOverPointColimitToDerived`. -/
instance categoryOverPointColimit_additive
    (C : Type u) [Category.{v} C] (A : Type w) [Category A] [Abelian A]
    [HasColimitsOfShape Cᵒᵖ A] :
    (colim : (Cᵒᵖ ⥤ A) ⥤ A).Additive := by
  have : PreservesBinaryBiproducts (colim : (Cᵒᵖ ⥤ A) ⥤ A) :=
    preservesBinaryBiproducts_of_preservesBinaryCoproducts _
  exact Functor.additive_of_preservesBinaryBiproducts _

/-- The homotopy-to-derived functor whose total left derived functor is the derived lower shriek
for the projection from a category over a point. -/
abbrev categoryOverPointColimitToDerived
    (C : Type u) [Category.{v} C] (A : Type w) [Category A] [Abelian A]
    [HasDerivedCategory A] [HasDerivedCategory (Cᵒᵖ ⥤ A)] [HasColimitsOfShape Cᵒᵖ A] :
    HomotopyCategory (Cᵒᵖ ⥤ A) (ComplexShape.up ℤ) ⥤ DerivedCategory A :=
  mapHomotopyCategoryToDerived (colim : (Cᵒᵖ ⥤ A) ⥤ A)

/-- The derived lower shriek functor `Lπ!` for the projection from a category over a point. -/
abbrev categoryOverPointDerivedColimit
    (C : Type u) [Category.{v} C] (A : Type w) [Category A] [Abelian A]
    [HasDerivedCategory A] [HasDerivedCategory (Cᵒᵖ ⥤ A)] [HasColimitsOfShape Cᵒᵖ A]
    [Functor.HasLeftDerivedFunctor
      (categoryOverPointColimitToDerived C A :
        HomotopyCategory (Cᵒᵖ ⥤ A) (ComplexShape.up ℤ) ⥤ DerivedCategory A)
      (HomotopyCategory.quasiIso (Cᵒᵖ ⥤ A) (ComplexShape.up ℤ))] :
    DerivedCategory (Cᵒᵖ ⥤ A) ⥤ DerivedCategory A :=
  Functor.totalLeftDerived
    (categoryOverPointColimitToDerived C A :
      HomotopyCategory (Cᵒᵖ ⥤ A) (ComplexShape.up ℤ) ⥤ DerivedCategory A)
    (DerivedCategory.Qh :
      HomotopyCategory (Cᵒᵖ ⥤ A) (ComplexShape.up ℤ) ⥤
        DerivedCategory (Cᵒᵖ ⥤ A))
    (HomotopyCategory.quasiIso (Cᵒᵖ ⥤ A) (ComplexShape.up ℤ))

/- Lean surface notation for the recurring derived lower shriek `Lπ!` attached to the
projection from a category over a point. The ambient category `C` and target abelian category
`A` remain explicit on the notation surface because they are the owner parameters of
`categoryOverPointDerivedColimit`. -/
scoped notation:max "Lπ![" C:max ", " A:max "]" => categoryOverPointDerivedColimit C A

end Derived

end CategoryTheory
