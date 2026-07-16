import Mathlib.Algebra.Homology.DerivedCategory.TStructure
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
import StacksProject_2024.stacks_project.Chap13.Definition_13_11_3

open CategoryTheory
open CategoryTheory.ObjectProperty
open DerivedCategory.TStructure

noncomputable section

universe u v

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

variable {A : Type u} [Category.{v} A] [Abelian A]

/-- The object property on `D(A)` consisting of those derived objects whose every cohomology
object lies in the chosen object property `P ⊆ A`. -/
abbrev derivedCategoryCohomologyInProperty
    (P : ObjectProperty A) : ObjectProperty (DerivedCategory A) :=
  fun K ↦ ∀ n : ℤ, P ((DerivedCategory.homologyFunctor A n).obj K)

/-- The full subcategory `D_P(A) ⊆ D(A)` cut out by requiring all cohomology objects to lie in
`P`. -/
abbrev DerivedCategoryWithCohomologyIn (P : ObjectProperty A) :=
  (derivedCategoryCohomologyInProperty P).FullSubcategory

scoped[DerivedCategoryWithCohomologyIn] notation3:max "D_{" P "}" =>
  DerivedCategoryWithCohomologyIn P

/-- The cohomology-in-`P` owner on the bounded-below derived category `D⁺(A)`. -/
abbrev derivedCategoryBoundedBelowCohomologyInProperty
    (P : ObjectProperty A) : ObjectProperty (D⁺(A)) :=
  (derivedCategoryCohomologyInProperty P).inverseImage
    ((t.plus : ObjectProperty (DerivedCategory A)).ι)

/-- The bounded-below derived subcategory `D^+_P(A) ⊆ D⁺(A)` cut out by `P`. -/
abbrev DerivedCategoryPlusWithCohomologyIn (P : ObjectProperty A) :=
  (derivedCategoryBoundedBelowCohomologyInProperty P).FullSubcategory

scoped[DerivedCategoryWithCohomologyIn] notation3:max "D⁺_{" P "}" =>
  DerivedCategoryPlusWithCohomologyIn P

open scoped DerivedCategoryWithCohomologyIn

namespace DerivedCategoryPlusWithCohomologyIn

variable {P : ObjectProperty A}

/-- The ambient bounded-below derived object underlying an object of
`DerivedCategoryPlusWithCohomologyIn P`. -/
abbrev toBoundedBelow (K : DerivedCategoryPlusWithCohomologyIn P) :=
  K.obj

/-- The ambient derived object underlying an object of
`DerivedCategoryPlusWithCohomologyIn P`. This is the canonical bridge/view from the
cohomology-in-`P` bounded-below owner to the unbounded derived category. -/
abbrev toDerived (K : DerivedCategoryPlusWithCohomologyIn P) :=
  K.obj.obj

end DerivedCategoryPlusWithCohomologyIn

/-- The cohomology-in-`P` owner on the bounded-above derived category `D⁻(A)`. -/
abbrev derivedCategoryBoundedAboveCohomologyInProperty
    (P : ObjectProperty A) : ObjectProperty (D⁻(A)) :=
  (derivedCategoryCohomologyInProperty P).inverseImage
    ((t.minus : ObjectProperty (DerivedCategory A)).ι)

/-- The bounded-above derived subcategory `D^-_P(A) ⊆ D⁻(A)` cut out by `P`. -/
abbrev DerivedCategoryMinusWithCohomologyIn (P : ObjectProperty A) :=
  (derivedCategoryBoundedAboveCohomologyInProperty P).FullSubcategory

scoped[DerivedCategoryWithCohomologyIn] notation3:max "D⁻_{" P "}" =>
  DerivedCategoryMinusWithCohomologyIn P

/-- The cohomology-in-`P` owner on the bounded derived category `Dᵇ(A)`. -/
abbrev derivedCategoryBoundedCohomologyInProperty
    (P : ObjectProperty A) : ObjectProperty (Dᵇ(A)) :=
  (derivedCategoryCohomologyInProperty P).inverseImage
    ((t.bounded : ObjectProperty (DerivedCategory A)).ι)

/-- The bounded derived subcategory `Dᵇ_P(A) ⊆ Dᵇ(A)` cut out by `P`. -/
abbrev DerivedCategoryBoundedWithCohomologyIn (P : ObjectProperty A) :=
  (derivedCategoryBoundedCohomologyInProperty P).FullSubcategory

scoped[DerivedCategoryWithCohomologyIn] notation3:max "Dᵇ_{" P "}" =>
  DerivedCategoryBoundedWithCohomologyIn P

end CategoryTheory
